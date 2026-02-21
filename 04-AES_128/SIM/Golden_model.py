# Golden_Model.py
from Crypto.Cipher import AES

# Read the data and key from the key.txt file
with open('key.txt', 'r') as file:
    data_hex = file.readline().strip() # Read the data hex string
    key_hex = file.readline().strip()  # Read the key hex string

    # Convert the hex strings to bytes
    data = bytes.fromhex(data_hex)
    key = bytes.fromhex(key_hex)

    # Create the AES cipher object in ECB mode
    cipher = AES.new(key, AES.MODE_ECB)

    # Encrypt the data
    ciphertext = cipher.encrypt(data)

    # Write the ciphertext to the output.txt file
    with open('output.txt', 'w') as file:
        file.write(ciphertext.hex())