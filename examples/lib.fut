
import "prelude"

let myget [n] 't (x : { i32(m) | m < n && 0 <= m}) (arr : [n]t) : t = arr[x]
