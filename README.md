# Suple a kilo

Comparador de precios de suplementos en Argentina.

- `index.html`: el sitio (buscador y comparación).
- `scraper.py`: busca precios en las tiendas y genera `datos.json` (lo que lee el sitio) y `precios.db` (historial).
- `.github/workflows/actualizar.yml`: corre el scraper todos los días y publica el sitio.

Mercado Libre necesita dos secretos en el repositorio: `ML_CLIENT_ID` y `ML_CLIENT_SECRET`.
