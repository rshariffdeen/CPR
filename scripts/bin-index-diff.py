import sys
import struct

file_path_a = sys.argv[1]
file_path_b = sys.argv[2]

byte_list_a = dict()
byte_list_b = dict()


with open(file_path_a, "rb") as file_a:
    byte = file_a.read(1)
    index_a = 0
    while byte:
        number = int(struct.unpack('>B', byte)[0])
        byte_list_a[index_a] = number
        index_a = index_a + 1
        byte = file_a.read(1)

with open(file_path_b, "rb") as file_b:
    byte = file_b.read(1)
    index_b = 0
    while byte:
        number = int(struct.unpack('>B', byte)[0])
        byte_list_b[index_b] = number
        index_b = index_b + 1
        byte = file_b.read(1)

diff_list = list()
for index in byte_list_a:
    if byte_list_a[index] != byte_list_b[index]:
        diff_list.append(index)

print(diff_list)

