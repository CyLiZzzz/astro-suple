# Suply

Comparador de precios de suplementos en Argentina.

- `index.html`: el sitio (buscador, filtros, fichas de producto, calculadora de duración).
- `scraper.py`: lee los precios de cada tienda y genera `datos.json` (lo que lee el sitio), `reporte.json` (qué pasó en cada tienda) y `precios.db` (historial).
- `.github/workflows/actualizar.yml`: corre el scraper todos los días y publica el sitio en GitHub Pages.

Opcional, en Settings > Secrets and variables > Actions:
- Secretos `ML_CLIENT_ID` y `ML_CLIENT_SECRET`: para sumar Mercado Libre.
- Variable `SCRAPER_CONTACTO`: un email de contacto que el scraper muestra a las tiendas.
