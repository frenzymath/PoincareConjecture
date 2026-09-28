import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Flow.Basic
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Topology.Algebra.Field









noncomputable section
set_option autoImplicit false

open Set Topology

namespace PoincareConjecture.Surgery.Terminal.Gluing

theorem exists_product_interval_avoiding_finite
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X × Ioo (-1 : ℝ) 1 → Y} (hf : IsOpenEmbedding f)
    {D : Set Y} (hD : D.Finite) :
    ∃ g : X × Ioo (-1 : ℝ) 1 → Y, IsOpenEmbedding g ∧
      range g ⊆ range f ∧ Disjoint (range g) D := by
  let A : Set ℝ := (fun p : X × Ioo (-1 : ℝ) 1 => p.2.val) '' (f ⁻¹' D)
  have hA : A.Finite := (hD.preimage hf.injective.injOn).image _
  obtain ⟨t, ht, htA⟩ := (Ioo_infinite (show (-1 : ℝ) < 1 by norm_num)).exists_notMem_finite hA
  have hopen : IsOpen (Ioo (-1 : ℝ) 1 ∩ Aᶜ) := isOpen_Ioo.inter hA.isClosed.isOpen_compl
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen t ⟨ht, htA⟩
  have hsmall (s : Ioo (-1 : ℝ) 1) : r * s.val + t ∈ Metric.ball t r := by
    rw [Metric.mem_ball, Real.dist_eq, add_sub_cancel_right, abs_mul,
      abs_of_pos hr]
    exact (mul_lt_mul_of_pos_left (abs_lt.mpr s.property) hr).trans_eq (mul_one r)
  let c : Ioo (-1 : ℝ) 1 → Ioo (-1 : ℝ) 1 :=
    fun s => ⟨r * s.val + t, (hball (hsmall s)).1⟩
  have hc : IsOpenEmbedding c := by
    apply IsOpenEmbedding.of_comp c isOpen_Ioo.isOpenEmbedding_subtypeVal
    exact (affineHomeomorph r t hr.ne').isOpenEmbedding.comp
      isOpen_Ioo.isOpenEmbedding_subtypeVal
  refine ⟨f ∘ Prod.map id c, hf.comp (IsOpenEmbedding.id.prodMap hc), ?_, ?_⟩
  · rintro _ ⟨p, rfl⟩
    exact ⟨Prod.map id c p, rfl⟩
  · apply Set.disjoint_left.mpr
    rintro _ ⟨p, rfl⟩ hp
    exact (hball (hsmall p.2)).2 ⟨Prod.map id c p, hp, rfl⟩

theorem exists_product_interval_in_compl
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T1Space Y]
    {f : X × Ioo (-1 : ℝ) 1 → Y} (hf : IsOpenEmbedding f)
    {D : Set Y} (hD : D.Finite) :
    ∃ g : X × Ioo (-1 : ℝ) 1 → (Dᶜ : Set Y), IsOpenEmbedding g := by
  obtain ⟨g, hg, -, hdisj⟩ := exists_product_interval_avoiding_finite hf hD
  let g' : X × Ioo (-1 : ℝ) 1 → (Dᶜ : Set Y) :=
    fun p => ⟨g p, Set.disjoint_left.mp hdisj ⟨p, rfl⟩⟩
  exact ⟨g', IsOpenEmbedding.of_comp g' hD.isClosed.isOpen_compl.isOpenEmbedding_subtypeVal hg⟩

theorem no_two_sided_projective_plane_of_punctured
    {S : GeneralizedSliceCarrier} {D : Set S.carrier} (hD : D.Finite)
    (h : ¬ ∃ f : RealProjectiveTwo × Ioo (-1 : ℝ) 1 → (Dᶜ : Set S.carrier),
      IsOpenEmbedding f) : SurgeryNoTwoSidedProjectivePlane S := by
  rintro ⟨f, hf⟩
  exact h (exists_product_interval_in_compl hf hD)

theorem no_two_sided_projective_plane_of_punctured_embedding
    {S T : GeneralizedSliceCarrier} {D : Set S.carrier} (hD : D.Finite)
    {e : (Dᶜ : Set S.carrier) → T.carrier} (he : IsOpenEmbedding e)
    (hT : SurgeryNoTwoSidedProjectivePlane T) : SurgeryNoTwoSidedProjectivePlane S := by
  apply no_two_sided_projective_plane_of_punctured hD
  rintro ⟨f, hf⟩
  exact hT ⟨e ∘ f, he.comp hf⟩

end PoincareConjecture.Surgery.Terminal.Gluing
