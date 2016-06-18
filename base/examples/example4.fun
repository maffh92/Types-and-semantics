let f = fn x => x + 1 in
let g = fn y => y * 2 in
let h = fn z => if true then f else g in
h f 3