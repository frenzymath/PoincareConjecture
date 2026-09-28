import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.OriginalTerminalEndCover
import Mathlib.Topology.Order.DenselyOrdered

set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76

theorem closed_two_sided_cover_frontier
    {X : Type*} [TopologicalSpace X] (E : Bool → Set X) (C : Set X)
    (hclosed : ∀ b, IsClosed (E b)) (hcover : E false ∪ E true = univ)
    (hinter : E false ∩ E true = C)
    (htwo : ∀ b, C ⊆ closure (E b \ C)) :
    ∀ b, interior (E b) = E b \ C ∧ frontier (E b) = C ∧
      closure (interior (E b)) = E b := by
  have one (A B : Set X) (hA : IsClosed A) (hB : IsClosed B)
      (hAB : A ∪ B = univ) (hAC : A ∩ B = C)
      (hCA : C ⊆ closure (A \ C)) (hCB : C ⊆ closure (B \ C)) :
      interior A = A \ C ∧ frontier A = C ∧ closure (interior A) = A := by
    have hdiff : A \ C = Bᶜ := by
      ext x
      have hc : x ∈ C ↔ x ∈ A ∧ x ∈ B := by rw [←hAC]; rfl
      have hu : x ∈ A ∨ x ∈ B := hAB.symm.subset (mem_univ x)
      simp only [mem_sdiff, mem_compl_iff, hc]
      tauto
    have hBC : B \ C ⊆ Aᶜ := by
      intro x hx ha
      exact hx.2 (hAC.subset ⟨ha,hx.1⟩)
    have hCnot : C ⊆ (interior A)ᶜ := by
      intro x hx
      have hh := closure_mono hBC (hCB hx)
      simpa only [closure_compl] using hh
    have hint : interior A = A \ C := by
      apply Subset.antisymm
      · intro x hx
        exact ⟨interior_subset hx, fun hc => hCnot hc hx⟩
      · apply interior_maximal sdiff_subset
        rw [hdiff]
        exact hB.isOpen_compl
    refine ⟨hint, ?_, ?_⟩
    · rw [frontier, hA.closure_eq, hint]
      ext x
      have hCA' : C ⊆ A := hAC.symm.subset.trans inter_subset_left
      simp only [mem_sdiff]
      constructor
      · tauto
      · intro hx
        exact ⟨hCA' hx, fun h => h.2 hx⟩
    · rw [hint]
      apply Subset.antisymm (closure_minimal sdiff_subset hA)
      intro x hx
      by_cases hc : x ∈ C
      · exact hCA hc
      · exact subset_closure ⟨hx,hc⟩
  intro b
  cases b
  · exact one _ _ (hclosed false) (hclosed true) hcover hinter (htwo false) (htwo true)
  · exact one _ _ (hclosed true) (hclosed false) (union_comm _ _ ▸ hcover)
      (inter_comm _ _ ▸ hinter) (htwo true) (htwo false)

theorem closed_cylinder_end_frontier
    {X Y Z : Type*} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace Y] [CompactSpace Y] [TopologicalSpace Z] [T2Space Z]
    {A T F : Set X} (hA : IsClosed A) (W : (Y × Icc (-1 : ℝ) 1) ≃ₜ T)
    (hcover : A ∪ T = F)
    (hends : ∀ z, (W z : X) ∈ A ↔ (z.2 : ℝ) = -1 ∨ (z.2 : ℝ) = 1)
    (p : C(X,Z)) (a : Bool → Z) (hai : Function.Injective a)
    (hpa : ∀ x ∈ A, p x = a false ∨ p x = a true)
    (hlabel : ∀ side y,
      p (W (y,⟨if side then 1 else -1,by cases side <;> norm_num⟩)) = a side) :
    let B := fun side : Bool => (fun z => (W z : X)) ''
      {z | if side then 0 ≤ (z.2 : ℝ) else (z.2 : ℝ) ≤ 0}
    let End := fun side : Bool => (A ∩ p ⁻¹' {a side}) ∪ B side
    let Core := (fun z => (W z : X)) '' {z | (z.2 : ℝ) = 0}
    ∀ side,
      interior ((Subtype.val : F → X) ⁻¹' End side) =
        (Subtype.val : F → X) ⁻¹' (End side \ Core) ∧
      frontier ((Subtype.val : F → X) ⁻¹' End side) =
        (Subtype.val : F → X) ⁻¹' Core ∧
      closure (interior ((Subtype.val : F → X) ⁻¹' End side)) =
        (Subtype.val : F → X) ⁻¹' End side := by
  intro B End Core
  obtain ⟨hclosed, hfull, hcommon⟩ := closed_cylinder_end_cover hA W hcover hends
    p a hai hpa hlabel
  let Es : Bool → Set F := fun side => Subtype.val ⁻¹' End side
  let Cs : Set F := Subtype.val ⁻¹' Core
  have heclosed : ∀ side, IsClosed (Es side) :=
    fun side => (hclosed side).preimage continuous_subtype_val
  have hefull : Es false ∪ Es true = univ := by
    ext x
    simp only [Es, mem_union, mem_preimage, mem_univ, iff_true]
    exact hfull.symm.subset x.property
  have hecommon : Es false ∩ Es true = Cs := by
    change Subtype.val ⁻¹' (End false ∩ End true) = Subtype.val ⁻¹' Core
    exact congrArg (fun D => (Subtype.val : F → X) ⁻¹' D) hcommon
  have hTF : T ⊆ F := fun x hx => hcover.subset (Or.inr hx)
  have htwo : ∀ side, Cs ⊆ closure (Es side \ Cs) := by
    intro side x hx
    obtain ⟨z, hz, hzx⟩ := hx
    let zero : Icc (-1 : ℝ) 1 := ⟨0,by norm_num⟩
    let g : Icc (-1 : ℝ) 1 → F := fun t => ⟨W (z.1,t),hTF (W (z.1,t)).property⟩
    have hg : Continuous g :=
      (continuous_subtype_val.comp (W.continuous.comp (continuous_const.prodMk continuous_id))).subtype_mk _
    have hg0 : g zero = x := by
      apply Subtype.ext
      have hzt : z.2 = zero := Subtype.ext hz
      change (W (z.1,zero) : X) = x
      rw [←hzt]
      exact hzx
    let V : Set (Icc (-1 : ℝ) 1) := if side then Ioi zero else Iio zero
    have hzV : zero ∈ closure V := by
      cases side
      · change zero ∈ closure (Iio zero)
        rw [closure_Iio' (show (Iio zero).Nonempty from ⟨⟨-1,by norm_num⟩,by
          change (-1 : ℝ) < 0; norm_num⟩)]
        change zero ≤ zero
        exact le_rfl
      · change zero ∈ closure (Ioi zero)
        rw [closure_Ioi' (show (Ioi zero).Nonempty from ⟨⟨1,by norm_num⟩,by
          change (0 : ℝ) < 1; norm_num⟩)]
        change zero ≤ zero
        exact le_rfl
    rw [←hg0]
    apply hg.continuousWithinAt.mem_closure hzV
    intro t ht
    refine ⟨?_, ?_⟩
    · change (W (z.1,t) : X) ∈ End side
      apply Or.inr
      refine ⟨(z.1,t), ?_, rfl⟩
      cases side
      · exact (show (t : ℝ) < 0 from ht).le
      · exact (show (0 : ℝ) < t from ht).le
    · rintro ⟨w, hw, heq⟩
      have hwt := congrArg Prod.snd (W.injective (Subtype.ext heq))
      have ht0 : (t : ℝ) = 0 := (congrArg Subtype.val hwt).symm.trans hw
      cases side
      · exact (ne_of_lt (show (t : ℝ) < 0 from ht)) ht0
      · exact (ne_of_gt (show (0 : ℝ) < t from ht)) ht0
  exact closed_two_sided_cover_frontier Es Cs heclosed hefull hecommon htwo

theorem HamiltonMarkedProtectedBall.original_labeled_end_frontier
    {ι κ α Y : Type*} [Fintype ι] [Fintype κ]
    [TopologicalSpace Y] [CompactSpace Y]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) (Fin 3 → ℝ)}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1) :
    let X := LatticeHandleAmbient ι κ L
    let R := latticeHandleDomain ι κ L
    let E := closure (R \ D)
    ∀ (W : (Y × Icc (-1 : ℝ) 1) ≃ₜ ↥(E ∩ D))
      (_hends : ∀ z, (W z : X) ∈ frontier R ↔ (z.2 : ℝ) = -1 ∨ (z.2 : ℝ) = 1)
      (a : Bool → sphere (0 : ι → ℝ) 1) (_ha : Function.Bijective a)
      (_hlabel : ∀ side y,
        (W (y,⟨if side then 1 else -1,by cases side <;> norm_num⟩) : X).1 = a side),
    let Core := (fun z => (W z : X)) '' {z | (z.2 : ℝ) = 0}
    let B := fun side : Bool => (fun z => (W z : X)) ''
      {z | if side then 0 ≤ (z.2 : ℝ) else (z.2 : ℝ) ≤ 0}
    let End := fun side : Bool =>
      {x : X | x ∈ E ∩ frontier R ∧ x.1 = a side} ∪ B side
    ∀ side,
      interior ((Subtype.val : frontier E → X) ⁻¹' End side) =
        (Subtype.val : frontier E → X) ⁻¹' (End side \ Core) ∧
      frontier ((Subtype.val : frontier E → X) ⁻¹' End side) =
        (Subtype.val : frontier E → X) ⁻¹' Core ∧
      closure (interior ((Subtype.val : frontier E → X) ⁻¹' End side)) =
        (Subtype.val : frontier E → X) ⁻¹' End side := by
  intro X R E W hends a ha hlabel Core B End
  let A := E ∩ frontier R
  have hA : IsClosed A := isClosed_closure.inter isClosed_frontier
  have hWends : ∀ z, (W z : X) ∈ A ↔ (z.2 : ℝ) = -1 ∨ (z.2 : ℝ) = 1 :=
    fun z => (and_iff_right (W z).property.1).trans (hends z)
  have hcover : A ∪ (E ∩ D) = frontier E := by
    obtain ⟨_, _, _, hcontact, _, _, hfront⟩ := b.closed_complement_geometry he hdim hi
    rw [hfront, ←hcontact]
    exact union_comm _ _
  let p : C(X,ι → ℝ) := ⟨Prod.fst, continuous_fst⟩
  let av : Bool → (ι → ℝ) := fun side => a side
  have hav : Function.Injective av := fun i j h => ha.1 (Subtype.ext h)
  have hpa : ∀ x ∈ A, p x = av false ∨ p x = av true := by
    intro x hx
    have hxS : x.1 ∈ sphere (0 : ι → ℝ) 1 := by
      have hh := hx.2
      change x ∈ frontier (closedBall (0 : ι → ℝ) 1 ×ˢ
        (univ : Set ((κ → ℝ) ⧸ L.toAddSubgroup))) at hh
      rw [frontier_prod_univ_eq, frontier_closedBall _ one_ne_zero] at hh
      exact hh.1
    obtain ⟨side, hside⟩ := ha.2 ⟨x.1,hxS⟩
    have hv := (congrArg Subtype.val hside).symm
    cases side
    · exact Or.inl hv
    · exact Or.inr hv
  exact closed_cylinder_end_frontier hA W hcover hWends p av hav hpa hlabel

end PoincareConjecture.M76
