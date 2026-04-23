#!/usr/bin/env python3
"""Extract base64 PNG from the saved MCP tool result, downsize, and save as a file."""
import base64
import json
import sys
import os

in_path = sys.argv[1]
out_path = sys.argv[2]

with open(in_path, 'r') as f:
    data = json.load(f)

img_b64 = data['result'][0]['data']
img_bytes = base64.b64decode(img_b64)

with open(out_path, 'wb') as f:
    f.write(img_bytes)

print(f"wrote {len(img_bytes)} bytes to {out_path}")
