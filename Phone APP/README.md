# Women Safety Shield Android app

This Android Studio project packages the phone-first interface in the APK. The phone calls the Flask API on the computer; Ollama and Qwen stay on the computer. The APK does not contain or start Ollama.

## Current state

- The mobile HTML is bundled at `app/src/main/assets/www/index.html` and served through AndroidX `WebViewAssetLoader`.
- The **Server** button stores the computer API address and the one-run pairing token locally on the phone.
- The **Test** button calls the computer's PIN-status endpoint to check the connection.
- Debug builds accept `http://` only for a private Wi-Fi IP or a `.local` hostname. Release builds require HTTPS.
- The computer API accepts private-network clients only, requires the pairing token, and keeps Ollama's port private.

## Computer setup for a local demo

1. Start Ollama and confirm the selected model is installed.
2. From the project root, run:

   ```powershell
   python .\safety_shield_all_in_one.py --phone-api --browser
   ```

3. Keep the phone and computer on the same trusted private Wi-Fi. Use the **Computer API address** and **Phone pairing token** printed in the computer console in the APK's **Server** settings.
4. If Windows Firewall asks, allow Python on **Private networks only**. Do not expose the port through router port-forwarding or use this HTTP debug connection on public Wi-Fi. The token authenticates the phone, but debug HTTP does not encrypt chat or location data.

The `--phone-api` option uses Flask's development server for a local prototype. It is not the production deployment mode. Before distributing a release APK, use a production WSGI server, HTTPS with a trusted certificate, and a production authentication/firewall setup. The release APK rejects HTTP addresses.

## Build

Open this folder in Android Studio and sync the project. It uses Android Gradle Plugin 9.4.1, Gradle 9.6.0, Android SDK 36, and Java 17. Choose **Build > Build APK(s)** for a debug APK. The APK is created at `app/build/outputs/apk/debug/app-debug.apk`.

The current development computer has Java but does not have Android Studio, the Android SDK, Gradle, or `adb`; therefore an APK cannot be built here until those tools are installed.

## Updating the bundled interface

`index.html` is extracted from the phone-first template in the root Python app. When that UI changes, regenerate the asset with the project's `tools/sync_mobile_ui.py` script before building the APK.
