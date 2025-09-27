# -*- coding: utf-8 -*-
"""
FTTH KMZ Builder — Road‑Aware, Building‑Snap (Single OLT, fixed ODC list)
Version: v1.7 (portable, Windows-friendly)

Input fixed dari script:
- Koordinat OLT dan 17 ODC di-hardcode dari link yang diberikan user.
- Parameter utama bisa diubah di blok CONFIG.

Output:
- KMZ: folderisasi OLT→Feeder→ODC→Distribusi→ODP.
- CSV: ringkasan titik dan panjang rute.

Catatan:
- Script ini mengambil data OSM via Overpass API (jalan + bangunan) di radius per ODC.
- Routing nempel jalan menggunakan NetworkX di graf jalan.
- ODP dipilih dari centroid bangunan terdekat, dengan jarak antar ODP ≥ min_odp_spacing_m.
- Jika tidak ditemukan 8 bangunan valid dalam radius, script memperluas radius bertahap.

Diuji pada Python 3.10–3.12 Windows. Jika modul belum ada, auto-install.
"""

import os, sys, math, json, time, subprocess, importlib, zipfile, io, csv, random
from pathlib import Path
from typing import List, Tuple, Dict, Any

# ---------------- Auto-install ----------------
REQS = [
    "requests>=2.32.3","shapely>=2.0.4","pyproj>=3.6.1","networkx>=3.2.1",
    "numpy>=1.26.4","simplekml>=1.3.6"
]

def ensure(req: str):
    try:
        importlib.import_module(req.split("==")[0].split(">=")[0])
    except ImportError:
        subprocess.check_call([sys.executable, "-m", "pip", "install", req])

for r in REQS:
    ensure(r)

import requests
import networkx as nx
import numpy as np
from shapely.geometry import LineString, Point, Polygon
from shapely.ops import unary_union
from pyproj import Transformer
import simplekml

# ---------------- Cache config ----------------
CACHE_DIR = Path(os.getenv("OVERPASS_CACHE_DIR", Path(__file__).resolve().parent / ".overpass_cache"))
CACHE_ENABLED = os.getenv("OVERPASS_CACHE_DISABLE", "").lower() not in {"1", "true", "yes"}
if CACHE_ENABLED:
    try:
        CACHE_DIR.mkdir(parents=True, exist_ok=True)
    except Exception:
        CACHE_ENABLED = False

# ---------------- CONFIG ----------------
OLT_NAME = "OLT"
OLT_LAT, OLT_LON = -6.120852, 106.503933

ODCS: List[Tuple[str,float,float]] = [
    ("ODC-01", -6.1209783, 106.5044971),
    ("ODC-02", -6.1230712, 106.5039610),
    ("ODC-03", -6.1234559, 106.5059254),
    ("ODC-04", -6.1245323, 106.5062184),
    ("ODC-05", -6.1255937, 106.5067099),
    ("ODC-06", -6.1184707, 106.5044039),
    ("ODC-07", -6.1179663, 106.5047244),
    ("ODC-08", -6.1175253, 106.5050982),
    ("ODC-09", -6.1161532, 106.5044894),
    ("ODC-10", -6.1187331, 106.5047197),
    ("ODC-11", -6.1201156, 106.5066988),
    ("ODC-12", -6.1202339, 106.5059720),
    ("ODC-13", -6.1213764, 106.5071654),
    ("ODC-14", -6.1195998, 106.5047505),
    ("ODC-15", -6.1188344, 106.5064447),
    ("ODC-16", -6.1175120, 106.5060578),
    ("ODC-17", -6.1190698, 106.5047546),
]

# Aturan
min_odp_spacing_m = 40.0
odp_per_odc = 8
start_radius_m = 250.0
max_radius_m = 600.0
radius_step_m = 150.0

# Styling
COLOR_FEEDER = (0x19, 0x76, 0xD2)  # #1976D2
COLOR_DISTRI  = (0xF5, 0x7C, 0x00)  # #F57C00

# ---------------- Helpers ----------------
WGS84 = "EPSG:4326"
# Local proj near Tangerang (UTM 48S fits West Java/West Banten roughly)
UTM48S = "EPSG:32748"
tr_w_to_l = Transformer.from_crs(WGS84, UTM48S, always_xy=True)
tr_l_to_w = Transformer.from_crs(UTM48S, WGS84, always_xy=True)

def to_local(lon: float, lat: float) -> Tuple[float,float]:
    x, y = tr_w_to_l.transform(lon, lat)
    return x, y

def to_wgs(x: float, y: float) -> Tuple[float,float]:
    lon, lat = tr_l_to_w.transform(x, y)
    return lon, lat


def _cache_file_name(lat: float, lon: float, radius_m: float) -> Path:
    key = f"{lat:.6f}_{lon:.6f}_{radius_m:.1f}.json"
    return CACHE_DIR / key


def overpass_query(lat: float, lon: float, radius_m: float) -> Dict[str, Any]:
    # Highways and buildings within radius
    q = f"""
    [out:json][timeout:60];
    (
      way["highway"](around:{int(radius_m)},{lat},{lon});
      relation["building"](around:{int(radius_m)},{lat},{lon});
      way["building"](around:{int(radius_m)},{lat},{lon});
      node["building"](around:{int(radius_m)},{lat},{lon});
    );
    out body center;
    >; out skel qt;
    """
    url = "https://overpass-api.de/api/interpreter"

    cache_file: Path | None = None
    if CACHE_ENABLED:
        cache_file = _cache_file_name(lat, lon, radius_m)
        if cache_file.exists():
            try:
                with cache_file.open("r", encoding="utf-8") as fh:
                    return json.load(fh)
            except Exception:
                try:
                    cache_file.unlink()
                except Exception:
                    pass

    for attempt in range(5):
        try:
            r = requests.post(url, data={"data": q}, timeout=90)
            if r.status_code == 429:
                time.sleep(2 + attempt)
                continue
            r.raise_for_status()
            data = r.json()
            if CACHE_ENABLED and cache_file is not None:
                try:
                    with cache_file.open("w", encoding="utf-8") as fh:
                        json.dump(data, fh)
                except Exception:
                    pass
            return data
        except Exception:
            time.sleep(2 + attempt)
    raise RuntimeError("Overpass request failed repeatedly")


def extract_ways_and_buildings(data: Dict[str, Any]):
    nodes = {}
    for el in data.get("elements", []):
        if el.get("type") == "node":
            nodes[el["id"]] = (el.get("lon"), el.get("lat"))

    roads: List[LineString] = []
    bldg_pts: List[Point] = []

    for el in data.get("elements", []):
        if el.get("type") == "way" and "highway" in el.get("tags", {}):
            coords = []
            for nid in el.get("nodes", []):
                if nid in nodes:
                    lon, lat = nodes[nid]
                    coords.append((lon, lat))
            if len(coords) >= 2:
                roads.append(LineString(coords))
        # buildings: prefer center if given, else polygon centroid
        if el.get("type") in ("way", "relation") and "building" in el.get("tags", {}):
            if "center" in el:
                lon, lat = el["center"]["lon"], el["center"]["lat"]
                bldg_pts.append(Point(lon, lat))
            else:
                # try centroid from nodes
                coords = []
                for nid in el.get("nodes", []):
                    if nid in nodes:
                        coords.append(nodes[nid])
                if len(coords) >= 3:
                    try:
                        poly = Polygon(coords)
                        c = poly.centroid
                        bldg_pts.append(Point(c.x, c.y))
                    except Exception:
                        pass
        if el.get("type") == "node" and "building" in el.get("tags", {}):
            lon, lat = el.get("lon"), el.get("lat")
            bldg_pts.append(Point(lon, lat))

    return roads, bldg_pts


def build_graph_from_roads(roads: List[LineString]) -> nx.Graph:
    G = nx.Graph()
    for ls in roads:
        coords = list(ls.coords)
        for i in range(len(coords)-1):
            (lon1, lat1) = coords[i]
            (lon2, lat2) = coords[i+1]
            x1, y1 = to_local(lon1, lat1)
            x2, y2 = to_local(lon2, lat2)
            w = math.hypot(x2-x1, y2-y1)
            G.add_node((x1,y1))
            G.add_node((x2,y2))
            G.add_edge((x1,y1), (x2,y2), weight=w)
    return G


def nearest_graph_node(G: nx.Graph, x: float, y: float) -> Tuple[float,float]:
    # simple linear scan; graph small per-ODC radius
    nodes = list(G.nodes)
    best = None
    bestd = 1e18
    for nxp, nyp in nodes:
        d = (nxp-x)**2 + (nyp-y)**2
        if d < bestd:
            bestd = d
            best = (nxp, nyp)
    return best


def route_length_m(G: nx.Graph, path: List[Tuple[float,float]]) -> float:
    L = 0.0
    for i in range(len(path)-1):
        x1,y1 = path[i]
        x2,y2 = path[i+1]
        L += math.hypot(x2-x1, y2-y1)
    return L


def shortest_path_xy(G: nx.Graph, src_xy: Tuple[float,float], dst_xy: Tuple[float,float]):
    s = nearest_graph_node(G, *src_xy)
    t = nearest_graph_node(G, *dst_xy)
    return nx.shortest_path(G, s, t, weight="weight")


def pack_odp_candidates(bldg_pts: List[Point], odc_lon: float, odc_lat: float,
                        need: int, min_spacing_m: float) -> List[Tuple[float,float]]:
    # Greedy: sort by distance from ODC, pick if spacing ok
    ox, oy = to_local(odc_lon, odc_lat)
    cands = []
    for p in bldg_pts:
        bx, by = to_local(p.x, p.y)
        d = math.hypot(bx-ox, by-oy)
        cands.append((d, bx, by))
    cands.sort(key=lambda t: t[0])

    chosen: List[Tuple[float,float]] = []
    for _, bx, by in cands:
        ok = True
        for (cx, cy) in chosen:
            if math.hypot(bx-cx, by-cy) < min_spacing_m:
                ok = False
                break
        if ok:
            chosen.append((bx, by))
            if len(chosen) >= need:
                break
    return chosen


def kml_color_abgr(rgb: Tuple[int,int,int], alpha: int = 255) -> str:
    r,g,b = rgb
    return f"{alpha:02x}{b:02x}{g:02x}{r:02x}"

# ---------------- Main build ----------------

def main():
    random.seed(42)
    out_dir = os.path.abspath(os.getcwd())
    kmz_name = "ftth_final.kmz"
    csv_name = "ftth_summary.csv"

    kml = simplekml.Kml()
    # Styles
    st_olt  = simplekml.Style()
    st_olt.iconstyle.icon.href = "http://maps.google.com/mapfiles/kml/shapes/star.png"
    st_olt.iconstyle.scale = 1.2

    st_odc  = simplekml.Style()
    st_odc.iconstyle.icon.href = "http://maps.google.com/mapfiles/kml/shapes/placemark_square.png"
    st_odc.iconstyle.scale = 1.1

    st_odp  = simplekml.Style()
    st_odp.iconstyle.icon.href = "http://maps.google.com/mapfiles/kml/shapes/placemark_circle.png"
    st_odp.iconstyle.scale = 0.9

    st_feeder = simplekml.Style()
    st_feeder.linestyle.color = kml_color_abgr(COLOR_FEEDER)
    st_feeder.linestyle.width = 3

    st_distri = simplekml.Style()
    st_distri.linestyle.color = kml_color_abgr(COLOR_DISTRI)
    st_distri.linestyle.width = 2

    f_olt = kml.newfolder(name="OLT")
    p_olt = f_olt.newpoint(name=OLT_NAME, coords=[(OLT_LON, OLT_LAT)])
    p_olt.style = st_olt

    f_feeder = kml.newfolder(name="Feeder (OLT→ODC)")

    # CSV init
    csv_rows = [["TYPE","NAME","LAT","LON","LEN_M","NOTES"]]
    csv_rows.append(["OLT", OLT_NAME, OLT_LAT, OLT_LON, "", "source"])

    # Build a single global road graph by merging per-ODC fetches
    global_roads: List[LineString] = []
    global_buildings: List[Point] = []

    # Fetch per ODC and extend global sets
    for name, lat, lon in ODCS:
        radius = start_radius_m
        got = False
        while radius <= max_radius_m:
            data = overpass_query(lat, lon, radius)
            roads, bpts = extract_ways_and_buildings(data)
            if len(roads) >= 5 and len(bpts) >= 20:
                global_roads.extend(roads)
                global_buildings.extend(bpts)
                got = True
                break
            radius += radius_step_m
        if not got:
            # still use what we have to avoid hard fail
            global_roads.extend(roads)
            global_buildings.extend(bpts)

    # Build graph
    G = build_graph_from_roads(global_roads)

    # Compute feeder routes
    olt_xy = to_local(OLT_LON, OLT_LAT)

    for name, lat, lon in ODCS:
        odc_xy = to_local(lon, lat)
        # Route OLT→ODC
        try:
            path = shortest_path_xy(G, olt_xy, odc_xy)
            Lm = route_length_m(G, path)
            coords = [to_wgs(x,y) for (x,y) in path]
            ls = f_feeder.newlinestring(name=f"Feeder {OLT_NAME}→{name}")
            ls.coords = coords
            ls.style = st_feeder
            csv_rows.append(["FEEDER", f"{OLT_NAME}->{name}", lat, lon, f"{Lm:.1f}", "road routing"])
        except Exception:
            # fallback straight line
            ls = f_feeder.newlinestring(name=f"Feeder {OLT_NAME}→{name} (fallback)")
            ls.coords = [(OLT_LON, OLT_LAT), (lon, lat)]
            ls.style = st_feeder
            Lm = LineString([(OLT_LON, OLT_LAT),(lon,lat)]).length * 111_320  # rough meters
            csv_rows.append(["FEEDER", f"{OLT_NAME}->{name}", lat, lon, f"{Lm:.1f}", "fallback straight"])

        # ODC node
        f_odc = kml.newfolder(name=name)
        p = f_odc.newpoint(name=name, coords=[(lon, lat)])
        p.style = st_odc

        # Select ODP candidates
        radius = start_radius_m
        chosen_xy: List[Tuple[float,float]] = []
        while radius <= max_radius_m and len(chosen_xy) < odp_per_odc:
            # filter buildings inside radius
            inside = []
            ox, oy = to_local(lon, lat)
            rloc = radius
            r2 = rloc*rloc
            for pt in global_buildings:
                bx, by = to_local(pt.x, pt.y)
                if (bx-ox)**2 + (by-oy)**2 <= r2:
                    inside.append(pt)
            chosen_xy = pack_odp_candidates(inside, lon, lat, odp_per_odc, min_odp_spacing_m)
            radius += radius_step_m

        # Draw distribution to ODP
        for i, (cx, cy) in enumerate(chosen_xy, 1):
            clon, clat = to_wgs(cx, cy)
            # point
            pt = f_odc.newpoint(name=f"{name}-ODP-{i:02d}", coords=[(clon, clat)])
            pt.style = st_odp

            # route ODC→ODP
            try:
                path = shortest_path_xy(G, odc_xy, (cx, cy))
                Lm = route_length_m(G, path)
                coords = [to_wgs(x,y) for (x,y) in path]
                ls = f_odc.newlinestring(name=f"Distribusi {name}→ODP-{i:02d}")
                ls.coords = coords
                ls.style = st_distri
                csv_rows.append(["DIST", f"{name}->ODP-{i:02d}", clat, clon, f"{Lm:.1f}", "road routing"])
            except Exception:
                ls = f_odc.newlinestring(name=f"Distribusi {name}→ODP-{i:02d} (fallback)")
                ls.coords = [(lon, lat), (clon, clat)]
                ls.style = st_distri
                Lm = LineString([(lon, lat),(clon,clat)]).length * 111_320
                csv_rows.append(["DIST", f"{name}->ODP-{i:02d}", clat, clon, f"{Lm:.1f}", "fallback straight"])

        # If less than required, add placeholders around ODC to meet 8
        idx = len(chosen_xy)
        while idx < odp_per_odc:
            idx += 1
            # ring 55 m placeholder
            ang = (idx-1) * (360.0/odp_per_odc)
            dx = 55.0*math.cos(math.radians(ang))
            dy = 55.0*math.sin(math.radians(ang))
            x = odc_xy[0] + dx
            y = odc_xy[1] + dy
            clon, clat = to_wgs(x, y)
            pt = f_odc.newpoint(name=f"{name}-ODP-{idx:02d} (PH)", coords=[(clon, clat)])
            pt.style = st_odp
            ls = f_odc.newlinestring(name=f"Distribusi {name}→ODP-{idx:02d} (PH)")
            ls.coords = [(lon, lat), (clon, clat)]
            ls.style = st_distri
            csv_rows.append(["DIST", f"{name}->ODP-{idx:02d}", clat, clon, "", "placeholder"])

    # Save KML and zip to KMZ
    kml_path = os.path.join(out_dir, "doc.kml")
    kml.save(kml_path)
    kmz_path = os.path.join(out_dir, kmz_name)
    with zipfile.ZipFile(kmz_path, "w", compression=zipfile.ZIP_DEFLATED) as z:
        z.write(kml_path, arcname="doc.kml")

    # CSV
    csv_path = os.path.join(out_dir, csv_name)
    with open(csv_path, "w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerows(csv_rows)

    # Cleanup temp KML
    try:
        os.remove(kml_path)
    except Exception:
        pass

    print("=== DONE ===")
    print("KMZ:", kmz_path)
    print("CSV:", csv_path)

if __name__ == "__main__":
    main()
