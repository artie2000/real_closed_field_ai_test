import importlib
for m in ['fitz', 'pypdfium2', 'pdf2image', 'PIL', 'PyPDF2', 'pdfminer']:
    try:
        mod = importlib.import_module(m)
        print(f'{m}: ok')
    except ImportError as e:
        print(f'{m}: missing')
