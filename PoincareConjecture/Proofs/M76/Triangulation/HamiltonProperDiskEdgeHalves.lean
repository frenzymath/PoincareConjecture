import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskEdgeRegion











set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "Cube" => closedBall (0 : V2) 1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  {R D : Set E} {b : Cube ≃ₜ D}





theorem HamiltonProperDiskTriangulation.exists_edge_signed_halves
    (T : HamiltonProperDiskTriangulation R D b) (h3 : Module.finrank ℝ E = 3)
    (hproper : ∀ x : Cube, (b x : E) ∈ frontier R ↔ (x : V2) ∈ sphere 0 1)
    (p : T.disk.vertices) {s : Finset E} (hps : (p : E) ∈ s)
    (hs : s ∈ T.disk.faces) (hcard : s.card = 2) :
    let f : E → ℝ := fun x => ((T.pairChart p).chart x).2
    IsFinitePLBallPair (ℝ × ℝ) (T.dualRegion s ∩ {x | f x ≤ 0})
        ((T.dualRegionRim s ∩ {x | f x ≤ 0}) ∪ (T.dualRegion s ∩ D)) ∧
      IsFinitePLBallPair (ℝ × ℝ) (T.dualRegion s ∩ {x | 0 ≤ f x})
        ((T.dualRegion s ∩ D) ∪ (T.dualRegionRim s ∩ {x | 0 ≤ f x})) ∧
      ∃ t ∈ T.disk.faces, ∃ u ∈ T.ambient.faces, ∃ v ∈ T.ambient.faces,
        s ⊆ t ∧ t.card = 3 ∧ t ⊆ u ∧ t ⊆ v ∧ u.card = 4 ∧ v.card = 4 ∧
        u.centroid ℝ id ∈ T.dualRegionRim s ∧
        v.centroid ℝ id ∈ T.dualRegionRim s ∧
        f (u.centroid ℝ id) < 0 ∧ 0 < f (v.centroid ℝ id) := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  let H := (T.pairChart p).chart
  let f : E → ℝ := fun x => (H x).2
  have hball := T.edge_region_ball h3 p hps hs hcard
  obtain ⟨a, z, haz, hW, hrim⟩ := T.exists_edge_zero_arc hproper hs hcard
  have hsource := T.dualRegion_subset_chart_source p hps
  have hzero (x : E) (hx : x ∈ T.dualRegion s) : x ∈ D ↔ f x = 0 := by
    rcases (T.pairChart p).model with ⟨_, hd⟩ | ⟨hr, hd⟩
    · exact hd x (hsource hx)
    · constructor
      · exact fun h => ((hd x (hsource hx)).mp h).2
      · exact fun h => (hd x (hsource hx)).mpr ⟨(hr x (hsource hx)).mp hx.2, h⟩
  have hWzero : T.dualRegion s ∩ {x | f x = 0} = T.dualRegion s ∩ D := by
    ext x
    exact and_congr_right (fun hx => (hzero x hx).symm)
  have hqzero : T.dualRegionRim s ∩ {x | f x = 0} = {a, z} := by
    calc
      T.dualRegionRim s ∩ {x | f x = 0} = T.dualRegionRim s ∩ D := by
        ext x
        exact and_congr_right (fun hx => (hzero x (hball.1 hx)).symm)
      _ = {a, z} := hrim
  obtain ⟨t, ht, hst, htc⟩ := T.exists_disk_triangle_coface hs
  obtain ⟨u, hu, v, hv, htu, htv, huc, hvc, hum, hvm, hun, hvp⟩ :=
    T.exists_edge_normal_witnesses h3 hproper p hps hs hcard ht htc hst
  have huRim : u.centroid ℝ id ∈ T.dualRegionRim s := Or.inl hum
  have hvRim : v.centroid ℝ id ∈ T.dualRegionRim s := Or.inl hvm
  have hcuts := hball.signed_halves_of_zero_arc f
    (H.continuousOn.mono hsource).snd hW haz hWzero hqzero
    ⟨u.centroid ℝ id, huRim, hun⟩ ⟨v.centroid ℝ id, hvRim, hvp⟩
  exact ⟨hcuts.1, hcuts.2, t, ht, u, hu, v, hv, hst, htc, htu, htv,
    huc, hvc, huRim, hvRim, hun, hvp⟩

end PoincareConjecture.M76.HamiltonIndexOne
