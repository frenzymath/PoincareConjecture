import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.CommonCollar.BoundaryLift
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.CommonCollar.AttachmentPL

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

theorem collar_mem_surface_iff_base
    {E X : Type*} {K D : Set E} {S : Set X} {a : ℝ} (ha : 0 < a)
    (c : E × ℝ → X) (hi : InjOn c (K ×ˢ Icc (0 : ℝ) a)) (hDK : D ⊆ K)
    (htrace : S ∩ c '' (K ×ˢ Ico (0 : ℝ) a) = c '' (D ×ˢ Ico (0 : ℝ) a))
    {x : E} (hx : x ∈ K) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) a) :
    c (x, t) ∈ S ↔ c (x, 0) ∈ c '' (D ×ˢ ({0} : Set ℝ)) := by
  have hxt : (x, t) ∈ K ×ˢ Icc (0 : ℝ) a := ⟨hx, ht.1, ht.2.le⟩
  have hx0 : (x, (0 : ℝ)) ∈ K ×ˢ Icc (0 : ℝ) a := ⟨hx, le_rfl, ha.le⟩
  constructor
  · intro hs
    obtain ⟨w, hw, heq⟩ := htrace.subset ⟨hs, ⟨(x, t), ⟨hx, ht⟩, rfl⟩⟩
    have he := hi ⟨hDK hw.1, hw.2.1, hw.2.2.le⟩ hxt heq
    exact ⟨(x, 0), ⟨(congrArg Prod.fst he) ▸ hw.1, rfl⟩, rfl⟩
  · rintro ⟨w, hw, heq⟩
    have hw0 : w.2 = 0 := hw.2
    have he := hi ⟨hDK hw.1, by rw [hw0]; exact ⟨le_rfl, ha.le⟩⟩ hx0 heq
    have hfst : w.1 = x := congrArg Prod.fst he
    have hxD : x ∈ D := hfst ▸ hw.1
    exact (htrace.superset ⟨(x, t), ⟨hxD, ht⟩, rfl⟩).1

theorem exists_original_common_collar_patch
    {E Z V X ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [TopologicalSpace X] {e : ι → OpenPartialHomeomorph X V}
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V)
    {K : Set E} {R : Set X} (HB : K ≃ₜ frontier R) {a r : ℝ}
    (hr : 0 < r) (hra : r < a)
    (c : E × ℝ → X) (hc : PolyhedralPLInCharts e c (K ×ˢ Icc (0 : ℝ) a))
    (hi : InjOn c (K ×ˢ Icc (0 : ℝ) a))
    (hbase : ∀ x : K, c (x, 0) = HB x)
    (hcR : MapsTo c (K ×ˢ Icc (0 : ℝ) a) R)
    (hcfront : ∀ z ∈ K ×ˢ Icc (0 : ℝ) a, c z ∈ frontier R ↔ z.2 = 0)
    (A : SimplicialComplex ℝ Z) (hA : A.faces.Finite)
    (u : Z → X) (hu : PolyhedralPLInCharts e u A.space)
    (hui : InjOn u A.space) (huB : MapsTo u A.space (frontier R)) :
    ∃ w : Z × ℝ → X,
      PolyhedralPLInCharts e w (A.space ×ˢ Icc (0 : ℝ) r) ∧
      InjOn w (A.space ×ˢ Icc (0 : ℝ) r) ∧
      MapsTo w (A.space ×ˢ Icc (0 : ℝ) r) R ∧
      (∀ z ∈ A.space, w (z, 0) = u z) ∧
      (∀ z ∈ A.space ×ˢ Icc (0 : ℝ) r, w z ∈ frontier R ↔ z.2 = 0) ∧
      ∀ (S : Set X) (D : Set E), D ⊆ K →
        S ∩ c '' (K ×ˢ Ico (0 : ℝ) a) = c '' (D ×ˢ Ico (0 : ℝ) a) →
        ∀ z ∈ A.space ×ˢ Icc (0 : ℝ) r,
          w z ∈ S ↔ u z.1 ∈ c '' (D ×ˢ ({0} : Set ℝ)) := by
  obtain ⟨b, hb, hbK, hbval⟩ := exists_original_collar_boundary_lift hcompat HB
    (hr.trans hra).le c hc hi hbase A hA u hu huB
  obtain ⟨J, hJ, hJs⟩ := A.exists_finite_interval_product hA hr
  let fst := (ContinuousLinearMap.fst ℝ Z ℝ).toContinuousAffineMap
  let snd := (ContinuousLinearMap.snd ℝ Z ℝ).toContinuousAffineMap
  have hbJ : FinitePiecewiseAffineOn (fun z : Z × ℝ => b z.1) J.space :=
    hb.comp ((J.affineOnFaces_affine fst).finitePiecewiseAffineOn hJ)
      (fun _ hz => (hJs.subset hz).1)
  let w (z : Z × ℝ) : X := c (b z.1, z.2)
  have hm (z : Z × ℝ) (hz : z ∈ A.space ×ˢ Icc (0 : ℝ) r) :
      (b z.1, z.2) ∈ K ×ˢ Icc (0 : ℝ) a := ⟨hbK hz.1, hz.2.1, hz.2.2.trans hra.le⟩
  refine ⟨w, ?_, ?_, (fun _ hz => hcR (hm _ hz)), ?_, ?_, ?_⟩
  · rw [← hJs]
    exact hc.comp_finitePiecewiseAffineOn J hJ
      (hbJ.prod_mk ((J.affineOnFaces_affine snd).finitePiecewiseAffineOn hJ))
      (fun _ hz => hm _ (hJs.subset hz))
  · intro z hz v hv heq
    have he := hi (hm _ hz) (hm _ hv) heq
    apply Prod.ext
    · apply hui hz.1 hv.1
      have he1 : b z.1 = b v.1 := congrArg Prod.fst he
      rw [← hbval _ hz.1, ← hbval _ hv.1, he1]
    · exact congrArg (fun q : E × ℝ => q.2) he
  · exact hbval
  · intro z hz
    exact hcfront _ (hm _ hz)
  · intro S D hDK htrace z hz
    exact (collar_mem_surface_iff_base (hr.trans hra) c hi hDK htrace (hbK hz.1)
      ⟨hz.2.1, hz.2.2.trans_lt hra⟩).trans (by rw [hbval _ hz.1])

end PoincareConjecture.M76
