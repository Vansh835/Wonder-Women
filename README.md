# Women Safety Shield

Women Safety Shield is a single-file Flask application with desktop and phone-first interfaces. Both interfaces share the same route planner, chat assistant, emergency contacts, and safety guards.

## What it can do

- Compare walking, driving, Delhi Metro, and bus route options using public or cached map data.
- Compare driving, walking, and Metro + walk for one trip, and mark each checked point with no nearby mapped place on the route map.
- Search saved map data for the closest police station and hospital near a named Delhi place. Coordinates can be searched offline; resolving a place name may need internet access. Coordinates work offline against saved tiles. Distances are straight-line and cache coverage may be incomplete.
- Plan driving or walking routes through an optional stop C; Metro and bus via stops are not supported yet.
- Colour sampled route stretches green when mapped places were nearby and red when the sample had no mapped place. These are map-data signals, not live observations of crowds.
- Show each route's score, travel time, nearby mapped police and hospital points, and the nearest tagged 24-hour place when that information exists. Help points are marked on the map with approximate distance from a checked route point.
- Compare a route's current score with a midday estimate. After local sunset, the app uses a date-specific offline sunset/sunrise calculation; common weekly OpenStreetMap opening-hour schedules adjust place weights when present, while missing or unsupported schedules use the existing estimates.
- Suggest a nearby cab pickup point by ranking mapped places for nearby activity and distance, then offer a route to it.
- Prepare an SMS to a saved trusted contact with cab driver and vehicle details plus a map link. The user reviews it and taps Open SMS to send; the app does not send messages itself.
- Set a check-in timer. On Android, a local notification opens a prepared SMS to the selected contact when the timer expires; the user still reviews and sends it. Desktop/browser reminders work while the app page is open.
- On a phone, monitor a planned route while the page stays open, prompt after a 200 m deviation, offer an arrival message, and watch for a low battery. SMS messages open for review and still need the user to send them; background monitoring depends on browser and device support.
- Store multiple trusted contact numbers and home/work place names in device-local storage. Saved places can be added to the route dropdowns.
- Show a coarse Delhi busy/empty overlay from cached OpenStreetMap places. Areas without cached data are omitted.
- Switch the interface between English and Hindi. Choose English, Hindi, or Hinglish speech recognition; the Android app falls back to the native speech recognizer when WebView speech input is unavailable.
- Compare 10 to 100 manually labelled busy/empty audit points with the mapped-place classification and show the agreement percentage and confusion counts.
- Import and export audit points as CSV, or tap the map to add labelled points stored in browser local storage.
- Use a flashing sound and vibration alarm, save an emergency card, and review recent trip scores on the device.
- Find nearby mapped places and offer a route from the user's shared current location to each result.
- Dictate a chat message with the microphone button in supported browsers; the transcript appears in the input field for review before sending.
- Provide SOS and emergency numbers, location-sharing tools, a PIN-protected emergency-state reset, and a fake-call feature.
- On Android, optionally open the SOS panel after a shake while the app is in the foreground. The existing fake incoming call can be started from Safety tools.
- Share a one-time map link for the phone's current coordinates using the system share sheet. The link does not keep updating as the person moves.
- Answer women's-safety questions with a local Ollama model; no hosted AI API key is required.

Route scores describe the available map data. They are not crime statistics, live surveillance, or a guarantee of safety. Emergency services remain the source of help in immediate danger.

## Route map and safety tools

The route heat colours show whether the route's sampled map points had mapped amenities nearby. A red segment means no matching place was found around that sample; it does not prove that the street is empty or unsafe. Green means mapped places were found, not that anyone is present now. Help-point distances are approximate, and a 24-hour venue is listed only when its OpenStreetMap record is tagged with 24-hour opening hours.

The daytime comparison recalculates mapped-place weighting for midday and is intended as a rough planning aid. The cab message and pickup suggestion are optional: check details and surroundings yourself, and send any SMS from your device.

Check-in messages are prepared for review. The app does not send SMS automatically. Contacts, timer state, and saved home/work place names are stored in browser or Android WebView local storage; selecting a saved place for a route sends that place name to the route service for planning. The audit comparison measures agreement with mapped-place presence on the supplied points, not real-world safety.

The app does not yet provide a continuously updating public location link or complete offline maps, routing, and place search. Route scoring can use previously cached place data, but the basemap, geocoding, and route geometry still need network access unless separately supplied and cached.

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
## GPU build for Windows without a virtual environment

Use `safety_shield_gpu.py` for the GPU-offload build. It asks Ollama to place as many model layers on the GPU as available memory allows (`OLLAMA_NUM_GPU=99`). Actual GPU use depends on the Ollama installation, graphics driver, and available VRAM; Ollama can fall back to CPU when needed. The app's Python/Flask code itself does not use the GPU; Ollama performs the model inference.

Run `run_gpu_no_venv.bat` from the extracted project folder. It uses the regular Python 3.10+ installation, offers to install the project's required packages for the current Windows user, checks for Ollama, downloads `qwen3:latest` if needed, then starts the phone-first app. No virtual environment is created. If the other computer has a different GPU or too little VRAM, set `OLLAMA_NUM_GPU` to a smaller value or remove the setting to let Ollama choose automatically.

The Pylance messages in the supplied diagnostics are static type-checker warnings. They are separate from runtime installation problems; creating a second file does not by itself clear those warnings.
