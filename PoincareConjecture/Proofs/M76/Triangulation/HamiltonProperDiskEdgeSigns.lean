import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskEdgeHalves










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "V" => (V2 × ℝ)
local notation "Cube" => closedBall (0 : V2) 1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  {R D : Set E} {b : Cube ≃ₜ D}
  {T : HamiltonProperDiskTriangulation R D b} {c : E ≃ᴬ[ℝ] V}





theorem HamiltonProperDiskNormalLabels.half_eq_on_edge_dual
    (O : HamiltonProperDiskNormalLabels T c)
    (hproper : ∀ x : Cube, (b x : E) ∈ frontier R ↔ (x : V2) ∈ sphere 0 1)
    (p q : T.disk.vertices) {s : Finset E} (hs : s ∈ T.disk.faces)
    (hsc : s.card = 2) (hps : (p : E) ∈ s) (hqs : (q : E) ∈ s) :
    T.dualRegion s ∩ {x | 0 ≤ O.height p x} =
      T.dualRegion s ∩ {x | 0 ≤ O.height q x} := by
  have h3 : Module.finrank ℝ E = 3 := by
    simpa [Module.finrank_prod] using c.toAffineEquiv.linear.finrank_eq
  let f : E → ℝ := fun x => ((T.pairChart p).chart x).2
  obtain ⟨hn, hp, t, ht, u, hu, v, hv, hst, htc, htu, htv,
      huc, hvc, hum, hvm, hun, hvp⟩ :=
    T.exists_edge_signed_halves h3 hproper p hps hs hsc
  have hball := T.edge_region_ball h3 p hps hs hsc
  have hpS := T.dualRegion_subset_chart_source p hps
  have hqS := T.dualRegion_subset_chart_source q hqs
  have huZ := hball.1 hum
  have hvZ := hball.1 hvm
  have huHull : u.centroid ℝ id ∈ convexHull ℝ (u : Set E) :=
    u.centroid_mem_convexHull (T.ambient.nonempty_of_mem_faces hu)
  have hvHull : v.centroid ℝ id ∈ convexHull ℝ (v : Set E) :=
    v.centroid_mem_convexHull (T.ambient.nonempty_of_mem_faces hv)
  have hDzero (x : E) (hx : x ∈ T.dualRegion s) (hxD : x ∈ D) : f x = 0 := by
    have hz : O.weight p * f x = 0 :=
      (O.height_eq_zero_iff p (hpS hx) hx.2).mpr hxD
    exact (mul_eq_zero.mp hz).resolve_left (O.nonzero p)
  have huD : u.centroid ℝ id ∉ D := fun hx =>
    (ne_of_lt hun) (hDzero _ huZ hx)
  have hvD : v.centroid ℝ id ∉ D := fun hx =>
    (ne_of_gt hvp) (hDzero _ hvZ hx)
  by_cases hweight : 0 < O.weight p
  · have hqpos := O.nonneg_on_half_of_incident_witness p q hp
      (fun _ hx => hx.1.2) (fun _ hx => hqS hx.1)
      (fun _ hx => Or.inl ⟨hx.1.1, hx.2⟩)
      ht htc (hst hps) (hst hqs) hv hvc htv ⟨hvZ, hvp.le⟩ hvHull
      (show 0 < O.height p (v.centroid ℝ id) from mul_pos hweight hvp) hvD
    have hqneg := O.nonpos_on_half_of_incident_witness p q hn
      (fun _ hx => hx.1.2) (fun _ hx => hqS hx.1)
      (fun _ hx => Or.inr ⟨hx.1.1, hx.2⟩)
      ht htc (hst hps) (hst hqs) hu huc htu ⟨huZ, hun.le⟩ huHull
      (show O.height p (u.centroid ℝ id) < 0 from mul_neg_of_pos_of_neg hweight hun) huD
    apply O.half_eq_of_whole_signs p q (fun _ hx => hx.2) hpS hqS
    · intro x hx
      have hraw : 0 ≤ f x := by
        by_contra h
        exact (not_lt_of_ge (show 0 ≤ O.weight p * f x from hx.2))
          (mul_neg_of_pos_of_neg hweight (lt_of_not_ge h))
      exact hqpos ⟨hx.1, hraw⟩
    · intro x hx
      have hraw : f x ≤ 0 := by
        by_contra h
        exact (not_lt_of_ge (show O.weight p * f x ≤ 0 from hx.2))
          (mul_pos hweight (lt_of_not_ge h))
      exact hqneg ⟨hx.1, hraw⟩
  · have hweight' : O.weight p < 0 :=
      lt_of_le_of_ne (le_of_not_gt hweight) (O.nonzero p)
    have hqpos := O.nonneg_on_half_of_incident_witness p q hn
      (fun _ hx => hx.1.2) (fun _ hx => hqS hx.1)
      (fun _ hx => Or.inr ⟨hx.1.1, hx.2⟩)
      ht htc (hst hps) (hst hqs) hu huc htu ⟨huZ, hun.le⟩ huHull
      (show 0 < O.height p (u.centroid ℝ id) from mul_pos_of_neg_of_neg hweight' hun) huD
    have hqneg := O.nonpos_on_half_of_incident_witness p q hp
      (fun _ hx => hx.1.2) (fun _ hx => hqS hx.1)
      (fun _ hx => Or.inl ⟨hx.1.1, hx.2⟩)
      ht htc (hst hps) (hst hqs) hv hvc htv ⟨hvZ, hvp.le⟩ hvHull
      (show O.height p (v.centroid ℝ id) < 0 from mul_neg_of_neg_of_pos hweight' hvp) hvD
    apply O.half_eq_of_whole_signs p q (fun _ hx => hx.2) hpS hqS
    · intro x hx
      have hraw : f x ≤ 0 := by
        by_contra h
        exact (not_lt_of_ge (show 0 ≤ O.weight p * f x from hx.2))
          (mul_neg_of_neg_of_pos hweight' (lt_of_not_ge h))
      exact hqpos ⟨hx.1, hraw⟩
    · intro x hx
      have hraw : 0 ≤ f x := by
        by_contra h
        exact (not_lt_of_ge (show O.weight p * f x ≤ 0 from hx.2))
          (mul_pos_of_neg_of_neg hweight' (lt_of_not_ge h))
      exact hqneg ⟨hx.1, hraw⟩

end PoincareConjecture.M76.HamiltonIndexOne
