import OAI.GroupTheory.ArtinCAT0.Main

-- Run with: lake env lean Check.lean
#print axioms OAI.ArtinCAT0.main
#print axioms OAI.ArtinCAT0.braid_eleven_squared
#check @OAI.ArtinCAT0.main
example : Fintype.card OAI.ArtinCAT0.Letters = 29 := by simp
