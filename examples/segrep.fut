import "repiota"
let segmented_replicate [n] (reps : [n]i32) (vs : [n]i32) : []i32 =
  unsafe let idxs = replicated_iota reps
  in map (\i -> vs[i]) idxs
let main [n] (reps : [n]i32) (vs : [n]i32) : []i32 =
  unsafe segmented_replicate reps vs
