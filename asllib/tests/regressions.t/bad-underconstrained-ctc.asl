func GetLastBit {N} (x: bits(N)) => bits(1)
begin
  return x[(N as integer {N - 1})];
end;

func main () => integer
begin
  - = GetLastBit{4}('1111');
  return 0;
end;
