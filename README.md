Reverse engineer Qianwen IME Android (`com.qianwen.ime` 1.1.37.1057).

## Usage

```shell
g++ -std=c++98 -Wall -Wextra -Ofast -static -o qw_dict qw_dict.cc
./qw_dict qw.table.bin qw.prism.bin dict.txt
```
