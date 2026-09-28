import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.AttachingDiskTopology
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneRetraction
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.MarkedCrossingBoundaryValues

set_option autoImplicit false
open Set Metric
namespace PoincareConjecture.M76

theorem exists_radial_retraction_of_embedded_ball
    {V Y : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [ProperSpace V]
    [TopologicalSpace Y] [T2Space Y]
    (q : V → Y) (hq : Continuous q) (hqo : IsOpenMap q)
    (hi : InjOn q (closedBall (0 : V) (3/2))) :
    ∃ r : C({y : Y // y ∉ q '' ball (0 : V) 1},
        {y : Y // y ∉ q '' ball (0 : V) (3/2)}),
      ∀ x : {y : Y // y ∉ q '' ball (0 : V) 1},
        (x : Y) ∉ q '' ball (0 : V) (3/2) → (r x : Y) = x := by
  classical
  let C := closedBall (0 : V) (3/2)
  let Z := (q '' ball (0 : V) 1)ᶜ
  let W := (q '' ball (0 : V) (3/2))ᶜ
  let f : C → q '' C := fun x => ⟨q x, x, x.property, rfl⟩
  have : CompactSpace C := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  have hf : Continuous f := (hq.comp continuous_subtype_val).subtype_mk _
  have hfi : Function.Injective f := by
    intro x y h
    exact Subtype.ext (hi x.property y.property (congrArg Subtype.val h))
  have hfs : Function.Surjective f := by
    rintro ⟨y,x,hx,rfl⟩
    exact ⟨⟨x,hx⟩,rfl⟩
  let H := (hf.isClosedEmbedding hfi).isEmbedding.toHomeomorphOfSurjective hfs
  have hH (y : q '' C) : q (H.symm y) = y :=
    congrArg Subtype.val (H.apply_symm_apply y)
  let s : Set Z := Subtype.val ⁻¹' (q '' C)
  let t : Set Z := Subtype.val ⁻¹' W
  have hs : IsClosed s := ((isCompact_closedBall (0 : V) (3/2)).image hq).isClosed.preimage
    continuous_subtype_val
  have ht : IsClosed t := (hqo _ isOpen_ball).isClosed_compl.preimage continuous_subtype_val
  have hcover : s ∪ t = univ := by
    apply eq_univ_of_forall
    intro x
    by_cases hx : x.val ∈ q '' ball (0 : V) (3/2)
    · exact Or.inl ((image_mono ball_subset_closedBall) hx)
    · exact Or.inr hx
  let v : s → V := fun x => H.symm ⟨x.val.val,x.property⟩
  have hv : Continuous v := continuous_subtype_val.comp (H.symm.continuous.comp
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _))
  have hvq (x : s) : q (v x) = x.val.val := hH _
  have hvnorm (x : s) : 1 ≤ ‖v x‖ := by
    by_contra hn
    exact x.val.property ⟨v x, mem_ball_zero_iff.mpr (lt_of_not_ge hn), hvq x⟩
  have hvne (x : s) : ‖v x‖ ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (hvnorm x))
  let w : s → V := fun x => ((3/2 : ℝ) / ‖v x‖) • v x
  have hw : Continuous w := (continuous_const.div (continuous_norm.comp hv) hvne).smul hv
  have hwnorm (x : s) : ‖w x‖ = 3/2 := by
    change ‖((3/2 : ℝ) / ‖v x‖) • v x‖ = 3/2
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact div_mul_cancel₀ _ (hvne x)
  have hwC (x : s) : w x ∈ C := mem_closedBall_zero_iff.mpr (hwnorm x).le
  have hwW (x : s) : q (w x) ∈ W := by
    rintro ⟨y,hy,hyq⟩
    have heq := hi (ball_subset_closedBall hy) (hwC x) hyq
    have hyn := mem_ball_zero_iff.mp hy
    rw [heq,hwnorm] at hyn
    exact (lt_irrefl _ hyn)
  let a : C(s,W) := ⟨fun x => ⟨q (w x),hwW x⟩, (hq.comp hw).subtype_mk _⟩
  let b : C(t,W) := ⟨fun x => ⟨x.val.val,x.property⟩, by fun_prop⟩
  have hagree (x : Z) (hxs : x ∈ s) (hxt : x ∈ t) :
      a ⟨x,hxs⟩ = b ⟨x,hxt⟩ := by
    let y : s := ⟨x,hxs⟩
    have hbound : ‖v y‖ ≤ 3/2 := mem_closedBall_zero_iff.mp (H.symm ⟨x,hxs⟩).property
    have hlow : 3/2 ≤ ‖v y‖ := by
      by_contra hn
      exact hxt ⟨v y,mem_ball_zero_iff.mpr (lt_of_not_ge hn),hvq y⟩
    have hn : ‖v y‖ = 3/2 := le_antisymm hbound hlow
    apply Subtype.ext
    change q (w y) = x.val
    have heq : w y = v y := by simp [w,hn]
    rw [heq]
    exact hvq y
  obtain ⟨r,_,hrt⟩ := HamiltonIndexOne.glue_closed_cover s t hs ht hcover a b hagree
  refine ⟨r,?_⟩
  intro x hx
  exact congrArg Subtype.val (hrt ⟨x,hx⟩)

theorem HamiltonMarkedProtectedBall.exists_punctured_torus_retraction
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) (Fin 3 → ℝ)}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D) (hpos : 0 < Fintype.card ι) :
    let q : (κ → ℝ) → (κ → ℝ) ⧸ L.toAddSubgroup := QuotientAddGroup.mk
    ∃ r : C({y // y ∉ q '' Metric.ball (0 : κ → ℝ) 1},
        {y // y ∉ q '' Metric.ball (0 : κ → ℝ) (3/2)}),
      ∀ x : {y // y ∉ q '' Metric.ball (0 : κ → ℝ) 1},
        (x : (κ → ℝ) ⧸ L.toAddSubgroup) ∉ q '' Metric.ball (0 : κ → ℝ) (3/2) →
        (r x : (κ → ℝ) ⧸ L.toAddSubgroup) = x := by
  exact exists_radial_retraction_of_embedded_ball QuotientAddGroup.mk
    QuotientAddGroup.continuous_mk
    (L.toAddSubgroup.isAddQuotientCoveringMap_of_comm
      DiscreteTopology.isDiscrete).isCoveringMap.isLocalHomeomorph.isOpenMap
    (b.quotient_injOn_attaching_disk hpos)

theorem HamiltonMarkedProtectedBall.exists_exterior_old_boundary_projection
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) (Fin 3 → ℝ)}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1)
    (a : sphere (0 : ι → ℝ) 1) :
    let E := closure (latticeHandleDomain ι κ L \ D)
    let q : (κ → ℝ) → (κ → ℝ) ⧸ L.toAddSubgroup := QuotientAddGroup.mk
    ∃ r : C(E, frontier E),
      (∀ x, (r x : LatticeHandleAmbient ι κ L).1 = a) ∧
      (∀ x, (r x : LatticeHandleAmbient ι κ L).2 ∉
        q '' Metric.ball (0 : κ → ℝ) (3/2)) ∧
      ∀ x : E, (x : LatticeHandleAmbient ι κ L).1 = a →
        (x : LatticeHandleAmbient ι κ L).2 ∉ q '' Metric.ball (0 : κ → ℝ) (3/2) →
        (r x : LatticeHandleAmbient ι κ L) = x := by
  classical
  let R := latticeHandleDomain ι κ L
  let E := closure (R \ D)
  let q : (κ → ℝ) → (κ → ℝ) ⧸ L.toAddSubgroup := QuotientAddGroup.mk
  obtain ⟨ρ,hρ⟩ := b.exists_punctured_torus_retraction (by omega)
  obtain ⟨hEO,_⟩ := b.exists_original_exterior_retraction_with_lateral he hdim hi
  have hER : E ⊆ R := by
    intro x hx
    exact (hEO hx).1
  have hproj (x : E) : (x.val).2 ∉ q '' Metric.ball (0 : κ → ℝ) 1 := by
    rintro ⟨z,hz,hzx⟩
    apply (hEO x.property).2
    exact ⟨(x.val.1,z),⟨(hER x.property).1,hz⟩,Prod.ext rfl hzx⟩
  let π : C(E,{y // y ∉ q '' Metric.ball (0 : κ → ℝ) 1}) :=
    ⟨fun x => ⟨x.val.2,hproj x⟩,by fun_prop⟩
  let f : C(E,LatticeHandleAmbient ι κ L) :=
    ⟨fun x => (a,(ρ (π x)).val),by fun_prop⟩
  have hfrontR (x : E) : f x ∈ frontier R := by
    change (a.val,_) ∈ frontier (closedBall (0 : ι → ℝ) 1 ×ˢ
      (univ : Set ((κ → ℝ) ⧸ L.toAddSubgroup)))
    rw [frontier_prod_univ_eq,frontier_closedBall _ one_ne_zero]
    exact ⟨a.property,mem_univ _⟩
  have hfE (x : E) : f x ∈ E :=
    b.old_boundary_outside_open_patch_mem_exterior he hdim hi (hfrontR x) (ρ (π x)).property
  have hfrontE (x : E) : f x ∈ frontier E := by
    rw [isClosed_closure.frontier_eq]
    refine ⟨hfE x,?_⟩
    intro hx
    exact (hfrontR x).2 (interior_mono hER hx)
  refine ⟨⟨fun x => ⟨f x,hfrontE x⟩,f.continuous.subtype_mk _⟩,
    fun _ => rfl,fun x => (ρ (π x)).property,?_⟩
  intro x ha hx
  exact Prod.ext ha.symm (hρ (π x) hx)

end PoincareConjecture.M76
