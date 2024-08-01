import Rake

def r:Rake := { d:=6, ks:=[5,7] } -- 5+6*n    7+6*n
--- partition:  5+6*n → 5+6*(0+5n)  5+6*(1+5n)  5+6*(2+5n)  |7+6*(3+5n)  5+6*(4+5n)
---                     5+30n       11+30n      17+30n      |25+5n
--                     5(1+6n)                              |5(5+n)5
#guard (r.partition 5).ks = [5, 7, 11, 13, 17, 19, 23, 25, 29, 31]
#guard r.terms 10 = (r.partition 5).terms 10
#eval r.terms 10
