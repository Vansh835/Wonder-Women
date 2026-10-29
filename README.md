# Women Safety Shield

Women Safety Shield is a single-file Flask application with desktop and phone-first interfaces. Both interfaces share the same route planner, chat assistant, emergency contacts, and safety guards.

## What it can do

- Plan available walking, driving, metro, and bus routes from cached or public map and routing data.
- Show mapped points of interest and explain the limits of route scores.
- Provide SOS options, trusted-contact tools, and a PIN-protected emergency-state reset.
- Run the chat model locally through Ollama; no hosted AI API key is required.

Route scores describe the available map data. They are not crime statistics, live surveillance, or a guarantee of safety. Emergency services remain the source of help in immediate danger.

## Requirements

- Python 3.10 or newer
- Ollama with a model installed
- Internet access for public map, geocoding, and routing services unless the required data is already cached

Install the Python dependencies:

```powershell
py -3 -m venv .venv
.\.venv\Scripts\python.exe -m pip install -r requirements.txt
```

Use `\.venv\Scripts\python.exe` for the commands below as well. This keeps the app's packages isolated from other Python projects and avoids depending on Windows' global `python` launcher registration. If `py -3` cannot find Python, install Python 3.10 or newer and select that interpreter in VS Code.

Install Ollama separately, then pull Qwen 3. The desktop and mobile interfaces both use `qwen3:latest` by default. To override it, set `OLLAMA_MODEL` before launching:

```powershell
ollama pull qwen3:latest
$env:OLLAMA_MODEL = "qwen3:latest"
```

## Run

Desktop interface:

```powershell
.\.venv\Scripts\python.exe safety_shield_all_in_one.py
```

Phone-first interface:

```powershell
.\.venv\Scripts\python.exe safety_shield_all_in_one.py --mobile
```

The desktop interface is served at `/`; the phone-first interface is served at `/mobile`. The app opens in a desktop window when `pywebview` is installed and otherwise opens in a browser. The local web server binds to loopback; it is intended for use on the same computer.

## Map data

These commands download or import data into local cache files:

```powershell
.\.venv\Scripts\python.exe safety_shield_all_in_one.py --download delhi
.\.venv\Scripts\python.exe safety_shield_all_in_one.py --download-metro
.\.venv\Scripts\python.exe safety_shield_all_in_one.py --download-lamps delhi
.\.venv\Scripts\python.exe safety_shield_all_in_one.py --import-osm path\to\map-data.zip
.\.venv\Scripts\python.exe safety_shield_all_in_one.py --import-bus path\to\gtfs-feed.zip
```

The bus import expects a complete GTFS feed with `routes.txt`, `trips.txt`, `stops.txt`, and `stop_times.txt`. For the optional desktop window and shapefile support, install `requirements-optional.txt`:

```powershell
.\.venv\Scripts\python.exe -m pip install -r requirements-optional.txt
```

Public OpenStreetMap-based services have their own usage policies, availability limits, and data coverage. Avoid repeated bulk requests. Cached information may be incomplete or old.

## Tests

Install development dependencies and run the guard regression suite:

```powershell
.\.venv\Scripts\python.exe -m pip install -r requirements-dev.txt
.\.venv\Scripts\python.exe -m ruff check safety_shield_all_in_one.py
.\.venv\Scripts\python.exe -m pytest -q
```

The suite uses the local Ollama Python package for app imports, but tests should not require a running Ollama server; model calls are stubbed in tests that need them.

## Local state and privacy

`safety_pin.json` stores a salted password hash, not the PIN itself. It and generated Python bytecode are local runtime artifacts and should not be committed. Map caches and evaluation files remain separate project data; keep or distribute them according to their source and intended use. The earlier split Python modules are retained as reference copies; the one-file build does not need to import them.
