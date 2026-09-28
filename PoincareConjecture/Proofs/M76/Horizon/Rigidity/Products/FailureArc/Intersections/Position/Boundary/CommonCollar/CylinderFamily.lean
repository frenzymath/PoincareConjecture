import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.CommonCollar.OriginalRegion
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.CommonCollar.AttachedCylinder










set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76

theorem PLDomain.exists_original_common_collared_cylinder_family
    {Z X ι T : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ Z] [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {R : Set X}
    (he : PLDomain e R) (hR : IsCompact R) (hconn : IsConnected R)
    (A : SimplicialComplex ℝ Z) (hA : A.faces.Finite)
    (f : T → ℝ × Z → X)
    (hf : ∀ i, PolyhedralPLInCharts e (f i) (Icc (-1 : ℝ) 1 ×ˢ A.space))
    (hfi : ∀ i, InjOn (f i) (Icc (-1 : ℝ) 1 ×ˢ A.space))
    (hfR : ∀ i, MapsTo (f i) (Icc (-1 : ℝ) 1 ×ˢ A.space) R)
    (hfB : ∀ i (b : Bool) z, z ∈ A.space → f i (if b then 1 else -1, z) ∈ frontier R) :
    ∃ (s : Finset R) (K : SimplicialComplex ℝ (s → ℝ × (Fin 3 → ℝ)))
      (HB : K.space ≃ₜ frontier R) (c : (s → ℝ × (Fin 3 → ℝ)) × ℝ → X)
      (a : ℝ) (rim : T → Bool → Z → (s → ℝ × (Fin 3 → ℝ)))
      (g : T → ℝ × Z → X),
      K.faces.Finite ∧ 0 < a ∧ a < 1 ∧
      PolyhedralPLInCharts e c (K.space ×ˢ Icc (0 : ℝ) 1) ∧
      IsEmbedding (fun z : (K.space ×ˢ Icc (0 : ℝ) 1) => c z) ∧
      MapsTo c (K.space ×ˢ Icc (0 : ℝ) 1) R ∧
      (∀ z : K.space, c (z, 0) = HB z) ∧
      (∀ z ∈ K.space ×ˢ Icc (0 : ℝ) 1, c z ∈ frontier R ↔ z.2 = 0) ∧
      IsOpen ((Subtype.val : R → X) ⁻¹' (c '' (K.space ×ˢ Ico (0 : ℝ) a))) ∧
      ∀ i,
        (∀ b, FinitePiecewiseAffineOn (rim i b) A.space) ∧
        (∀ b, MapsTo (rim i b) A.space K.space) ∧
        (∀ b z, z ∈ A.space → c (rim i b z, 0) = f i (if b then 1 else -1, z)) ∧
        PolyhedralPLInCharts e (g i) (Icc (-2 : ℝ) 2 ×ˢ A.space) ∧
        InjOn (g i) (Icc (-2 : ℝ) 2 ×ˢ A.space) ∧
        MapsTo (g i) (Icc (-2 : ℝ) 2 ×ˢ A.space) R ∧
        (∀ z ∈ Icc (-2 : ℝ) 2 ×ˢ A.space, g i z ∈ frontier R ↔ z.1 = -2 ∨ z.1 = 2) ∧
        (∀ (b : Bool) z, z ∈ A.space → g i (if b then 2 else -2, z) = f i (if b then 1 else -1, z)) ∧
        (g i '' (Icc (-2 : ℝ) 2 ×ˢ A.space)) ∩ (c '' (K.space ×ˢ Ico (0 : ℝ) a)) =
          c '' (((rim i false '' A.space) ∪ (rim i true '' A.space)) ×ˢ Ico (0 : ℝ) a) := by
  obtain ⟨s, K, HB, c, eps, G, hK, heps, heps1, hc, hi, hm, hb, hp,
    hGi, hGPL, hGrange, hGval, _, hGint, ho⟩ :=
    he.exists_original_common_collar_compression hR hconn
  obtain ⟨x₀, hx₀⟩ := hconn.nonempty
  have ha : 0 < eps / 2 := half_pos heps
  have ha1 : eps / 2 < 1 := (half_lt_self heps).trans heps1
  have hci : InjOn c (K.space ×ˢ Icc (0 : ℝ) 1) := by
    intro x hx y hy heq
    exact congrArg Subtype.val (hi.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) heq)
  have hGlevel : ∀ z : K.space,
      (G ⟨c (z, 0), hm _ ⟨z.property, by norm_num⟩⟩ : X) = c (z, eps / 2) := by
    intro z
    simpa only [zero_div, add_zero] using
      hGval ⟨(z, 0), ⟨z.property, le_rfl, heps.le⟩⟩ _ rfl
  have hGgap : ∀ x : R, (G x : X) ∉ c '' (K.space ×ˢ Ico (0 : ℝ) (eps / 2)) :=
    fun x => (hGrange.subset ⟨x, rfl⟩).2
  have hGinterior : ∀ x : R, (G x : X) ∈ interior R := fun x => hGint ⟨x, rfl⟩
  have hfamily := fun i => exists_original_collar_attached_cylinder he ⟨x₀, hx₀⟩ K hK HB
    c ha ha1.le hc hci hm hb (fun z hz => hp ⟨z, hz⟩) G hGi hGPL hGlevel hGgap hGinterior
    A hA (f i) (hf i) (hfi i) (hfR i) (hfB i)
  choose rim g hg using hfamily
  exact ⟨s, K, HB, c, eps / 2, rim, g, hK, ha, ha1, hc, hi, hm, hb,
    fun z hz => hp ⟨z, hz⟩, ho _ ha (half_le_self heps.le), hg⟩

end PoincareConjecture.M76
