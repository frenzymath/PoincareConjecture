import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Products.ProductCellEndNeighborhoods
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-!
# The actual boundary-near punctured product end

The punctured closed-ball product together with its explicit
boundary-near region is the complement of its actual central
cell. A literal interior chart of the closed-ball factor
transfers the compact deleted-cell end construction to this
original compact product. See Hamilton 1976, p. 66 and M76
derivation 270. No PL boundary extension or end cutting is
asserted here.
-/

set_option autoImplicit false

open Set Metric

namespace OpenPartialHomeomorph

/-- The identity on a positive open ball defines an actual
chart into its closed-ball subtype. The inverse is literal
subtype inclusion; the forward map is totalized at zero only
outside the closed ball. See the original handle-product end
calculation in Hamilton p. 66 and M76 derivation 270. -/
theorem exists_closedBall_interior_chart {E : Type*} [NormedAddCommGroup E]
    {R : ℝ} (hR : 0 < R) :
    ∃ J : OpenPartialHomeomorph E (closedBall (0 : E) R),
      J.source = ball (0 : E) R ∧ J.target = Subtype.val ⁻¹' ball (0 : E) R ∧
      (∀ x ∈ ball (0 : E) R, (J x : E) = x) ∧
      ∀ x : closedBall (0 : E) R, J.symm x = (x : E) := by
  classical
  let f : E → closedBall (0 : E) R := fun x =>
    if hx : x ∈ closedBall (0 : E) R then ⟨x, hx⟩ else ⟨0, mem_closedBall_self hR.le⟩
  have hf (x : E) (hx : x ∈ closedBall (0 : E) R) : (f x : E) = x := by
    simp only [f, dif_pos hx]
  have hfc : ContinuousOn f (ball (0 : E) R) := by
    apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
    exact continuousOn_id.congr (fun x hx => hf x (ball_subset_closedBall hx))
  let J : OpenPartialHomeomorph E (closedBall (0 : E) R) :=
    { toFun := f
      invFun := Subtype.val
      source := ball (0 : E) R
      target := Subtype.val ⁻¹' ball (0 : E) R
      map_source' := fun x hx => by
        change (f x : E) ∈ ball (0 : E) R
        rwa [hf x (ball_subset_closedBall hx)]
      map_target' := fun _ hx => hx
      left_inv' := fun x hx => hf x (ball_subset_closedBall hx)
      right_inv' := fun x _ => Subtype.ext (hf x x.property)
      open_source := isOpen_ball
      open_target := isOpen_ball.preimage continuous_subtype_val
      continuousOn_toFun := hfc
      continuousOn_invFun := continuous_subtype_val.continuousOn }
  exact ⟨J, rfl, rfl, fun x hx => hf x (ball_subset_closedBall hx), fun _ => rfl⟩

end OpenPartialHomeomorph

/-- The original punctured product and its boundary-near
region are exactly the complement of the central closed
cell. This is a literal subset identity in the original
compact product. See Hamilton p. 66 and M76 derivation 270. -/
theorem collared_punctured_product_eq_compl_cell
    {E Y : Type*} [NormedAddCommGroup E] (R r : ℝ) (q : Y) :
    ((univ : Set (closedBall (0 : E) R)) ×ˢ {q}ᶜ) ∪
      ({x : closedBall (0 : E) R | r < ‖(x : E)‖} ×ˢ (univ : Set Y)) =
      {z : closedBall (0 : E) R × Y | ‖(z.1 : E)‖ ≤ r ∧ z.2 = q}ᶜ := by
  ext z
  simp only [mem_union, mem_prod, mem_univ, true_and, and_true, mem_compl_iff,
    mem_singleton_iff, mem_setOf_eq, not_and_or, not_le]
  exact or_comm

/-- The exact punctured product with its boundary-near
region is open in the original closed-ball product topology.
See Hamilton p. 66 and M76 derivation 270. -/
theorem isOpen_collared_punctured_product
    {E Y : Type*} [NormedAddCommGroup E] [TopologicalSpace Y] [T1Space Y]
    (R r : ℝ) (q : Y) :
    IsOpen (((univ : Set (closedBall (0 : E) R)) ×ˢ {q}ᶜ) ∪
      ({x : closedBall (0 : E) R | r < ‖(x : E)‖} ×ˢ (univ : Set Y))) :=
  (isOpen_univ.prod isClosed_singleton.isOpen_compl).union
    ((isOpen_lt continuous_const continuous_subtype_val.norm).prod isOpen_univ)

namespace OpenPartialHomeomorph

/-- The actual closed-ball product with a puncture and a
boundary-near region has compact protected cores with simply
connected deleted-cell ends. Its literal central cell and
original compact ambient product are retained. The protected
set may include the whole original boundary. See Hamilton
p. 66 and M76 derivation 270. -/
theorem exists_compact_closedBall_deleted_cell_core
    {E F Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    (hdim : 2 < Module.finrank ℝ (E × F)) (Q : OpenPartialHomeomorph F Y)
    (h0 : (0 : F) ∈ Q.source) {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    {A : Set (closedBall (0 : E) R × Y)} (hA : IsCompact A)
    (hdis : Disjoint A {z | ‖(z.1 : E)‖ ≤ r ∧ z.2 = Q 0}) :
    ∃ K : Set (closedBall (0 : E) R × Y), IsCompact K ∧ A ⊆ interior K ∧
      Disjoint K {z | ‖(z.1 : E)‖ ≤ r ∧ z.2 = Q 0} ∧
      IsSimplyConnected (Kᶜ \ {z | ‖(z.1 : E)‖ ≤ r ∧ z.2 = Q 0}) := by
  obtain ⟨J, hJs, _, hJ, _⟩ := exists_closedBall_interior_chart (E := E) (hr.trans_lt hrR)
  let T := J.prod Q
  have hsource : closedBall (0 : E) r ×ˢ {(0 : F)} ⊆ T.source := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    change x ∈ J.source ∧ y ∈ Q.source
    refine ⟨?_, ?_⟩
    · rw [hJs]
      exact closedBall_subset_ball hrR hx
    · have hy0 : y = 0 := hy
      rwa [hy0]
  have himage : T '' (closedBall (0 : E) r ×ˢ {(0 : F)}) =
      {z : closedBall (0 : E) R × Y | ‖(z.1 : E)‖ ≤ r ∧ z.2 = Q 0} := by
    ext z
    constructor
    · rintro ⟨⟨x, y⟩, hxy, rfl⟩
      have hy0 : y = 0 := hxy.2
      change ‖(J x : E)‖ ≤ r ∧ Q y = Q 0
      rw [hJ x (closedBall_subset_ball hrR hxy.1), hy0]
      exact ⟨mem_closedBall_zero_iff.mp hxy.1, rfl⟩
    · intro hz
      refine ⟨((z.1 : E), 0), ⟨mem_closedBall_zero_iff.mpr hz.1, rfl⟩, ?_⟩
      apply Prod.ext
      · exact Subtype.ext (hJ z.1 (closedBall_subset_ball hrR
          (mem_closedBall_zero_iff.mpr hz.1)))
      · exact hz.2.symm
  simpa only [himage] using T.exists_compact_core_simplyConnected_deleted_cell_complement
    hdim hr hsource hA (by rwa [himage])

end OpenPartialHomeomorph
