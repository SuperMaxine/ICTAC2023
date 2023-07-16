import shutil
import re

# 假设你的__init__.py文件在当前目录下
src_file = "../automatark/complexnew/__init__.py"

# 假设你的文件夹名称是0-134
folder_names = ["data"+str(i) for i in range(803)]

# 假设你要替换的字符串是"complexnew"
pattern = "complexnew"

# 遍历每个文件夹
for folder in folder_names:
    # 拼接目标文件路径
    dst_file = folder + "/" + src_file[25:]
    # 复制文件到目标文件夹
    shutil.copyfile(src_file, dst_file)
    # 读取目标文件内容
    with open(dst_file, "r") as f:
        content = f.read()
    # 替换内容中的字符串为文件夹名称
    new_content = re.sub(pattern, folder, content)
    # 写入新的内容到目标文件
    with open(dst_file, "w") as f:
        f.write(new_content)
