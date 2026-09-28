import PoincareConjecture.Proofs.M76.Rigidity.InwardCollarCoordinates

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "I" => Icc (0 : ℝ) 1

theorem exists_finitePL_boundary_disk_collar_parameter
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {N : Set X} {j : V2 → X}
    (hcompat : ∀ i k, (e i).symm.trans (e k) ∈ piecewiseAffineGroupoid V3)
    (hj : PolyhedralPLInCharts e j D) (hjB : MapsTo j D (frontier N))
    (L : SimplicialComplex ℝ E) (hL : L.faces.Finite)
    (HB : L.space ≃ₜ frontier N) (c : E × ℝ → X)
    (hc : PolyhedralPLInCharts e c (L.space ×ˢ I))
    (hi : Topology.IsEmbedding (fun z : (L.space ×ˢ I : Set (E × ℝ)) => c z))
    (hbase : ∀ x : L.space, c ((x : E), 0) = HB x) :
    ∃ q : V2 → E, FinitePiecewiseAffineOn q D ∧
      ∀ x : D, q x = (HB.symm ⟨j x, hjB x.property⟩ : E) := by
  classical
  let q : V2 → E := fun x =>
    if hx : x ∈ D then HB.symm ⟨j x, hjB hx⟩ else 0
  have hqval (x : D) : q x = (HB.symm ⟨j x, hjB x.property⟩ : E) := by
    simp only [q, dif_pos x.property]
  have hqcont : ContinuousOn q D := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have h := continuous_subtype_val.comp (HB.symm.continuous.comp
      (hj.continuousOn.domRestrict.subtype_mk (fun x => hjB x.property)))
    convert h using 1
    funext x
    exact hqval x
  have hqmap : MapsTo q D L.space := by
    intro x hx
    rw [hqval ⟨x, hx⟩]
    exact (HB.symm ⟨j x, hjB hx⟩).property
  have hbasePL : PolyhedralPLInCharts e (fun z => c (z, 0)) L.space :=
    PolyhedralPLInCharts.finite_product_slice L hL hc (by norm_num)
  have hbaseInj : InjOn (fun z => c (z, 0)) L.space := by
    intro x hx y hy hxy
    have hpairs := congrArg Subtype.val (hi.injective
      (a₁ := ⟨(x, 0), ⟨hx, by norm_num⟩⟩)
      (a₂ := ⟨(y, 0), ⟨hy, by norm_num⟩⟩) hxy)
    exact congrArg Prod.fst hpairs
  have hcomposite : PolyhedralPLInCharts e ((fun z => c (z, 0)) ∘ q) D :=
    hj.congr (by
      intro x hx
      change j x = c (q x, 0)
      rw [hqval ⟨x, hx⟩, hbase, HB.apply_symm_apply])
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKD, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_unit_cube (ι := Fin 2)
  have h := hbasePL.finitePiecewiseAffineOn_lift hcompat hbaseInj K hK
    (hqcont.mono hKD.subset) (fun _ hx => hqmap (hKD.subset hx))
    (hKD.symm ▸ hcomposite)
  exact ⟨q, hKD ▸ h, hqval⟩

end PoincareConjecture.M76.Dehn
