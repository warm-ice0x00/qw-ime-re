# Reverse engineer Qianwen IME Android

Version: `com.qianwen.ime` 1.1.40.1060

## Usage

```shell
g++ -std=c++98 -Wall -Wextra -Ofast -static -o qw_dict qw_dict.cc
./qw_dict qw.table.bin qw.prism.bin dict.txt
```
