#!/usr/bin/env python3
"""Render PDF pages to images at a lower resolution by downscaling existing output."""
import base64
import json
import os
import sys

try:
    from PIL import Image
    import io
except ImportError:
    print("PIL missing")
    sys.exit(1)

# Try pypdfium2 for direct rendering
try:
    import pypdfium2 as pdfium
    HAS_PDFIUM = True
except ImportError:
    HAS_PDFIUM = False

PDF_PATH = "/data/clones/artie2000/real_closed_field_ai_test/rcf-equiv-conds/numina/blueprints/rcf-equiv-conds/source/rcf-equiv-conds-source.pdf"
OUT_DIR = "/data/clones/artie2000/real_closed_field_ai_test/rcf-equiv-conds/tmp-pages"

os.makedirs(OUT_DIR, exist_ok=True)

if HAS_PDFIUM:
    print("Using pypdfium2")
    pdf = pdfium.PdfDocument(PDF_PATH)
    for i in range(len(pdf)):
        page = pdf[i]
        img = page.render(scale=1.3).to_pil()
        img.save(f"{OUT_DIR}/page-{i+1}.png")
        print(f"rendered page {i+1}: {img.size}")
else:
    print("No pdfium available; trying other methods")
