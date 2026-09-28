import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.MarkedCoreAngularMap
import PoincareConjecture.Proofs.M76.Rigidity.OriginalBallTopology
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.OriginalProtectedExterior
import Mathlib.Topology.TietzeExtension

set_option autoImplicit false
open Set Metric Geometry
open scoped Topology
namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (-1 : ℝ) 1
local notation "B2" => closedBall (0 : P2) 1

private theorem exists_square_extension
    {X : Type*} [TopologicalSpace X] [NormalSpace X]
    {A : Set X} (hA : IsClosed A) (f : C(A,B2)) :
    ∃ F : C(X,B2), ∀ x : A, F x = f x := by
  let f₁ : C(A,ℝ) := ⟨fun x => (f x : P2).1,by fun_prop⟩
  let f₂ : C(A,ℝ) := ⟨fun x => (f x : P2).2,by fun_prop⟩
  obtain ⟨g₁,h₁⟩ := f₁.exists_restrict_eq hA
  obtain ⟨g₂,h₂⟩ := f₂.exists_restrict_eq hA
  let clip : ℝ → ℝ := fun t => max (-1) (min 1 t)
  have hc : Continuous clip := continuous_const.max (continuous_const.min continuous_id)
  have hb (t : ℝ) : |clip t| ≤ 1 := abs_le.mpr
    ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩
  let F : C(X,B2) := ⟨fun x => ⟨(clip (g₁ x),clip (g₂ x)),by
    rw [mem_closedBall_zero_iff,Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs]
    exact max_le (hb _) (hb _)⟩,by fun_prop⟩
  refine ⟨F,?_⟩
  intro x
  apply Subtype.ext
  have hf := (f x).property
  rw [mem_closedBall_zero_iff,Prod.norm_def,max_le_iff,Real.norm_eq_abs,
    Real.norm_eq_abs,abs_le,abs_le] at hf
  have hg₁ : g₁ x = (f x : P2).1 := congrArg (fun h : C(A,ℝ) => h x) h₁
  have hg₂ : g₂ x = (f x : P2).2 := congrArg (fun h : C(A,ℝ) => h x) h₂
  change (clip (g₁ x),clip (g₂ x)) = (f x : P2)
  rw [hg₁,hg₂]
  simp only [clip,min_eq_right hf.1.2,max_eq_right hf.1.1,
    min_eq_right hf.2.2,max_eq_right hf.2.1,Prod.mk.eta]

theorem HamiltonMarkedProtectedBall.exists_old_boundary_detector
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1) :
    ∃ F : C(↥(D ∪ frontier (latticeHandleDomain ι κ L)),(κ→ℝ) ⧸ L.toAddSubgroup),
      (∀ x, (x.val).1 = (fun _ => -1) → F x = (x.val).2) ∧
      ∀ x, (x.val ∈ D ∨ (x.val).1 = (fun _ => 1)) →
        F x ∈ (QuotientAddGroup.mk : (κ→ℝ) → (κ→ℝ) ⧸ L.toAddSubgroup) ''
          closedBall (0 : κ→ℝ) (3/2) := by
  classical
  obtain ⟨hι⟩ := Fintype.card_eq_one_iff_nonempty_unique.mp hi
  let : Unique ι := hι
  let X := LatticeHandleAmbient ι κ L
  let R := latticeHandleDomain ι κ L
  let Z := D ∪ frontier R
  let T := (κ→ℝ) ⧸ L.toAddSubgroup
  let Am : Set X := {x | x.1 = (fun _ => -1)}
  let Ap : Set X := {x | x.1 = (fun _ => 1)}
  have hm : D ∩ frontier R = hamiltonAttachingBlock ι κ L (3/2) := by
    rcases b.position with ⟨hz,_⟩ | ⟨_,_,_,_,_,hm⟩
    · omega
    · exact hm
  have hfront : frontier R = Am ∪ Ap := by
    dsimp only [R,latticeHandleDomain]
    rw [frontier_prod_univ_eq,frontier_closedBall _ (by norm_num : (1:ℝ) ≠ 0)]
    ext x
    have hconst : x.1 = (fun _ => x.1 default) :=
      funext (fun i => congrArg x.1 (Subsingleton.elim i default))
    simp only [mem_prod,mem_univ,and_true,mem_sphere_zero_iff_norm,mem_union,
      Am,Ap]
    have hn : ‖x.1‖ = |x.1 default| := by
      conv_lhs => rw [hconst]
      simp only [pi_norm_const,Real.norm_eq_abs]
    rw [hn,abs_eq (by norm_num : (0:ℝ) ≤ 1)]
    constructor
    · rintro (h|h)
      · exact Or.inr (hconst.trans (by rw [h]))
      · exact Or.inl (hconst.trans (by rw [h]))
    · rintro (h|h)
      · exact Or.inr (congrFun h default)
      · exact Or.inl (congrFun h default)
  have hAp : IsClosed Ap := isClosed_eq continuous_fst continuous_const
  have hAm : IsClosed Am := isClosed_eq continuous_fst continuous_const
  have hne : Disjoint Am Ap := by
    apply disjoint_left.mpr
    intro x hx hy
    have hh := congrFun (hx.symm.trans hy) default
    norm_num at hh
  obtain ⟨P,hends,hlat⟩ := b.exists_original_disk_cylinder_product he hdim hi
  let k : C(D,B2) := ⟨fun x => (P.symm x).2,by fun_prop⟩
  let a : C(B2,T) := ⟨fun z => (P (⟨-1,by norm_num⟩,z)).val.2,by fun_prop⟩
  have ha (z : B2) : a z ∈ (QuotientAddGroup.mk : (κ→ℝ) → T) ''
      closedBall (0 : κ→ℝ) (3/2) := by
    have hh := (hends false (⟨-1,by norm_num⟩,z)).mpr (by simp)
    obtain ⟨w,hw,hwP⟩ := hh
    exact ⟨w.2,hw.2,congrArg Prod.snd hwP⟩
  have hak (x : D) (hx : x.val ∈ Am) : a (k x) = x.val.2 := by
    have hxF : x.val ∈ frontier R := hfront.symm.subset (Or.inl hx)
    obtain ⟨w,hw,hwx⟩ := hm.subset ⟨x.property,hxF⟩
    have hwfirst : w.1 = (fun _ : ι => -1) := (congrArg Prod.fst hwx).trans hx
    have hxneg : x.val ∈ hamiltonMarkedProjection ι κ L ''
        ({fun _ : ι => -1} ×ˢ closedBall (0 : κ→ℝ) (3/2)) :=
      ⟨w,⟨hwfirst,hw.2⟩,hwx⟩
    have hz : ((P.symm x).1 : ℝ) = -1 :=
      (hends false (P.symm x)).mp (by simpa only [P.apply_symm_apply,Bool.false_eq_true,
        if_false] using hxneg)
    have hp : (⟨-1,by norm_num⟩,k x) = P.symm x :=
      Prod.ext (Subtype.ext hz.symm) rfl
    change (P (⟨-1,by norm_num⟩,k x)).val.2 = x.val.2
    rw [hp,P.apply_symm_apply]
  let B : Set Ap := (Subtype.val : Ap → X) ⁻¹' D
  let f : C(B,B2) := ⟨fun x => k ⟨x.val.val,x.property⟩,by fun_prop⟩
  obtain ⟨g,hg⟩ := exists_square_extension
    (b.ball.isCompact.isClosed.preimage continuous_subtype_val) f
  let F : Z → T := fun x => if hx : x.val ∈ D then a (k ⟨x.val,hx⟩)
    else if hp : x.val ∈ Ap then a (g ⟨x.val,hp⟩) else x.val.2
  have hFD (x : Z) (hx : x.val ∈ D) : F x = a (k ⟨x.val,hx⟩) := by simp [F,hx]
  have hFP (x : Z) (hx : x.val ∈ Ap) : F x = a (g ⟨x.val,hx⟩) := by
    by_cases hd : x.val ∈ D
    · rw [hFD x hd,hg ⟨⟨x.val,hx⟩,hd⟩]
      rfl
    · simp [F,hd,hx]
  have hFN (x : Z) (hx : x.val ∈ Am) : F x = x.val.2 := by
    by_cases hd : x.val ∈ D
    · rw [hFD x hd]
      exact hak _ hx
    · simp [F,hd,show x.val ∉ Ap from fun h => disjoint_left.mp hne hx h]
  have hcontD : ContinuousOn F ((Subtype.val : Z → X) ⁻¹' D) := by
    rw [continuousOn_iff_continuous_domRestrict]
    let j : ((Subtype.val : Z → X) ⁻¹' D) → D := fun x => ⟨x.val.val,x.property⟩
    have hj : Continuous j := by fun_prop
    exact (a.continuous.comp (k.continuous.comp hj)).congr (fun x => (hFD x.val x.property).symm)
  have hcontP : ContinuousOn F ((Subtype.val : Z → X) ⁻¹' Ap) := by
    rw [continuousOn_iff_continuous_domRestrict]
    let j : ((Subtype.val : Z → X) ⁻¹' Ap) → Ap := fun x => ⟨x.val.val,x.property⟩
    have hj : Continuous j := by fun_prop
    exact (a.continuous.comp (g.continuous.comp hj)).congr (fun x => (hFP x.val x.property).symm)
  have hcontN : ContinuousOn F ((Subtype.val : Z → X) ⁻¹' Am) :=
    (continuous_snd.comp continuous_subtype_val).continuousOn.congr (fun x hx => hFN x hx)
  have hcont : Continuous F := by
    have hc := (hcontD.union_of_isClosed hcontN
      (b.ball.isCompact.isClosed.preimage continuous_subtype_val)
      (hAm.preimage continuous_subtype_val)).union_of_isClosed hcontP
      ((b.ball.isCompact.isClosed.preimage continuous_subtype_val).union
        (hAm.preimage continuous_subtype_val)) (hAp.preimage continuous_subtype_val)
    have hcover : (((Subtype.val : Z → X) ⁻¹' D) ∪
        ((Subtype.val : Z → X) ⁻¹' Am)) ∪ ((Subtype.val : Z → X) ⁻¹' Ap) = univ := by
      ext x
      simp only [mem_union,mem_preimage,mem_univ,iff_true]
      rcases x.property with h | h
      · exact Or.inl (Or.inl h)
      · rcases hfront.subset h with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
    rw [hcover] at hc
    exact continuousOn_univ.mp hc
  refine ⟨⟨F,hcont⟩,hFN,?_⟩
  intro x hx
  rcases hx with hx | hx
  · change F x ∈ _
    rw [hFD x hx]
    exact ha _
  · change F x ∈ _
    rw [hFP x hx]
    exact ha _

theorem HamiltonMarkedProtectedBall.exists_original_exterior_boundary_detector
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1) :
    ∃ F : C(frontier (closure (latticeHandleDomain ι κ L \ D)),
        (κ→ℝ) ⧸ L.toAddSubgroup),
      (∀ x, (x.val).1 = (fun _ => -1) → F x = (x.val).2) ∧
      ∀ x, (x.val ∈ D ∨ (x.val).1 = (fun _ => 1)) →
        F x ∈ (QuotientAddGroup.mk : (κ→ℝ) → (κ→ℝ) ⧸ L.toAddSubgroup) ''
          closedBall (0 : κ→ℝ) (3/2) := by
  obtain ⟨F,hneg,hsmall⟩ := b.exists_old_boundary_detector he hdim hi
  obtain ⟨_,_,_,_,_,_,hfront⟩ := b.closed_complement_geometry he hdim hi
  have hsub : frontier (closure (latticeHandleDomain ι κ L \ D)) ⊆
      D ∪ frontier (latticeHandleDomain ι κ L) := by
    intro x hx
    rcases hfront.subset hx with ht | ho
    · exact Or.inl (b.ball.isCompact.isClosed.frontier_subset ht.1)
    · exact Or.inr ho.2
  let j : C(frontier (closure (latticeHandleDomain ι κ L \ D)),
      ↥(D ∪ frontier (latticeHandleDomain ι κ L))) :=
    ⟨fun x => ⟨x.val,hsub x.property⟩,by fun_prop⟩
  exact ⟨F.comp j,fun x hx => hneg (j x) hx,fun x hx => hsmall (j x) hx⟩

end PoincareConjecture.M76
