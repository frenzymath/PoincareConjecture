import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.ProductSurfaceLinks
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.MarkedLowerRimImage
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Surfaces.TwoBoundaryCount

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric Geometry BrownCollar PLAnnularStrip

namespace PoincareConjecture.M76

open Classical in
theorem exists_marked_attachment_annulus
    {ι κ E : Type*} [Fintype ι] [Fintype κ] [Unique κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hi : Fintype.card ι = 2)
    (P : (sphere (0 : ι → ℝ) 1 ×ˢ closedBall (0 : κ → ℝ) (3 / 2)) ≃ₜ K.space)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (C : Bool → SimplicialComplex ℝ E) (hCK : ∀ i, C i ≤ K)
    (gamma : ∀ i, sphere (0 : Fin 2 → ℝ) 1 ≃ₜ (C i).space)
    (hgamma : ∀ i, (gamma i).IsFinitePL)
    (hmark : ∀ i, (C i).space = range (fun x : sphere (0 : ι → ℝ) 1 =>
      (P ⟨((x : ι → ℝ), fun _ : κ => if i then (3 / 2 : ℝ) else -(3 / 2 : ℝ)),
        x.property, by
          rw [mem_closedBall_zero_iff, pi_norm_const, Real.norm_eq_abs]
          cases i <;> norm_num⟩ : E)))
    (hboundary : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard =
        if ∃ i, s ∈ (C i).faces then 1 else 2) :
    ∃ A : squareAnnulus 8 1 ≃ₜ K.space, A.IsFinitePL ∧
      (∀ p : squareAnnulus 8 1, depth 8 (p : ℝ × ℝ) = -1 ↔
        (A p : E) ∈ (C false).space) ∧
      (∀ p : squareAnnulus 8 1, depth 8 (p : ℝ × ℝ) = 1 ↔
        (A p : E) ∈ (C true).space) := by
  classical
  obtain ⟨g⟩ := exists_unit_sphere_circle_homeomorph hi
  have : PathConnectedSpace (Icc (0 : ℝ) 1) :=
    isPathConnected_iff_pathConnectedSpace.mp
      ((convex_Icc (0 : ℝ) 1).isPathConnected ⟨0, by norm_num⟩)
  let H : (Circle × Icc (0 : ℝ) 1) ≃ₜ K.space :=
    (g.symm.prodCongr (Homeomorph.refl _)).trans (markedProductCylinder P)
  have : PathConnectedSpace K.space := H.surjective.pathConnectedSpace H.continuous
  have hconn : IsPathConnected K.space := isPathConnected_iff_pathConnectedSpace.mpr inferInstance
  let f : sphere (0 : ι → ℝ) 1 → (C false).space := fun x =>
    ⟨(markedLowerRimMap (Y := K.space) P x).val, by
      rw [hmark false]
      exact ⟨x, by simp [markedLowerRimMap]⟩⟩
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp (P.continuous.comp
      ((continuous_subtype_val.prodMk continuous_const).subtype_mk _))
  have hfi : Function.Injective f := by
    intro x y h
    have hh : markedLowerRimMap P x = markedLowerRimMap P y :=
      Subtype.ext (congrArg (fun z : (C false).space => (z : E)) h)
    have hh' := P.injective hh
    exact Subtype.ext (congrArg
      (fun z : sphere (0 : ι → ℝ) 1 ×ˢ closedBall (0 : κ → ℝ) (3 / 2) => z.val.1) hh')
  have hfs : Function.Surjective f := by
    intro y
    obtain ⟨x,hx⟩ := (hmark false).subset y.property
    exact ⟨x,Subtype.ext hx⟩
  let e := Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective f ⟨hfi,hfs⟩) hf
  let i := ContinuousMap.inclusion (SimplicialComplex.space_subset_of_le (hCK false))
  let b : (C false).space := e (g.symm 1)
  obtain ⟨hgen,c,hsource,hbase⟩ := marked_product_lower_rim_data P e i
    (fun _ => Subtype.ext rfl) b
  have hdis : Disjoint (C false).space (C true).space := by
    rw [disjoint_left]
    intro z hz hz'
    obtain ⟨x,hx⟩ := (hmark false).subset hz
    obtain ⟨y,hy⟩ := (hmark true).subset hz'
    have h := P.injective (Subtype.ext (hx.trans hy.symm))
    have hh := congrArg
      (fun z : sphere (0 : ι → ℝ) 1 ×ˢ closedBall (0 : κ → ℝ) (3 / 2) => z.val.2 default) h
    norm_num at hh
  exact HamiltonIntervalTorus.exists_annulus_of_generating_boundary K hK hpure
    (connected_links_of_marked_annulus_product K hK hi P) hconn C hCK gamma hgamma
    hdis hboundary b hgen (fun _ => ⟨c, by rw [hsource]; trivial,
      fun a _ => hbase a⟩)

end PoincareConjecture.M76
