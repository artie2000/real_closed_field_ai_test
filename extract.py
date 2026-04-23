import json, base64, sys

input_file = sys.argv[1]
output_file = sys.argv[2]

with open(input_file) as f:
    data = json.load(f)
img = data['result'][0]
b = base64.b64decode(img['data'])
with open(output_file, 'wb') as o:
    o.write(b)
print(f'Wrote {len(b)} bytes to {output_file}')
