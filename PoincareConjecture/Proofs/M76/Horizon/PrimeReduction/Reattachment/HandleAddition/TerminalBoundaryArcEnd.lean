import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.AttachingDiskTopology
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneRetraction
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.EssentialAnnulusBarrier

set_option autoImplicit false
open Set Metric unitInterval
namespace PoincareConjecture.M76

theorem exists_radial_quotient_collar_embedding
    {Y κ : Type*} [TopologicalSpace Y] [Fintype κ]
    (L : Submodule ℤ (κ → ℝ)) [DiscreteTopology L]
    {r : ℝ} (hr : 0 < r)
    (hinj : InjOn (QuotientAddGroup.mk : (κ → ℝ) → (κ → ℝ) ⧸ L.toAddSubgroup)
      (closedBall 0 r))
    (v : C(Y,κ → ℝ)) (hvi : Function.Injective v) (hvn : ∀ y, ‖v y‖ = r) :
    ∃ F : C(Y × I,(κ → ℝ) ⧸ L.toAddSubgroup),
      Function.Injective F ∧
      (∀ y, F (y,0) = QuotientAddGroup.mk (v y)) ∧
      (∀ z, F z = QuotientAddGroup.mk ((1 - (z.2 : ℝ)/2) • v z.1)) ∧
      ∀ z, F z ∈ (QuotientAddGroup.mk : (κ → ℝ) → (κ → ℝ) ⧸ L.toAddSubgroup) ''
        ball 0 r ↔ (z.2 : ℝ) ≠ 0 := by
  let w : Y × I → κ → ℝ := fun z => (1 - (z.2 : ℝ)/2) • v z.1
  have hc : Continuous w := by fun_prop
  have hpos (z : Y × I) : 0 < 1 - (z.2 : ℝ)/2 := by
    have := z.2.property.2
    linarith
  have hn (z : Y × I) : ‖w z‖ = (1 - (z.2 : ℝ)/2) * r := by
    change ‖(1 - (z.2 : ℝ)/2) • v z.1‖ = _
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (hpos z),hvn]
  have hw (z : Y × I) : w z ∈ closedBall 0 r := by
    rw [mem_closedBall_zero_iff,hn]
    have := z.2.property.1
    nlinarith
  let F : C(Y × I,(κ → ℝ) ⧸ L.toAddSubgroup) :=
    ⟨fun z => QuotientAddGroup.mk (w z),QuotientAddGroup.continuous_mk.comp hc⟩
  refine ⟨F,?_,?_,fun _ => rfl,?_⟩
  · intro z z' hh
    have heq : w z = w z' := hinj (hw z) (hw z') hh
    have hnorm := congrArg norm heq
    rw [hn,hn] at hnorm
    have ht : (z.2 : ℝ) = z'.2 := by nlinarith
    have hv : v z.1 = v z'.1 := by
      apply smul_right_injective (κ → ℝ) (hpos z).ne'
      change (1 - (z.2 : ℝ)/2) • v z.1 = (1 - (z.2 : ℝ)/2) • v z'.1
      simpa only [w,←ht] using heq
    exact Prod.ext (hvi hv) (Subtype.ext ht)
  · intro y
    change QuotientAddGroup.mk ((1 - ((0 : I) : ℝ)/2) • v y) = _
    simp
  · intro z
    constructor
    · rintro ⟨x,hx,hxF⟩ hz
      have heq : x = w z := hinj (ball_subset_closedBall hx) (hw z) hxF
      have hh := mem_ball_zero_iff.mp hx
      rw [heq,hn,hz] at hh
      linarith
    · intro hz
      refine ⟨w z,?_,rfl⟩
      rw [mem_ball_zero_iff,hn]
      have ht := lt_of_le_of_ne z.2.property.1 (Ne.symm hz)
      nlinarith

theorem exists_closed_annular_end_embedding
    {X Y κ : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Fintype κ]
    (L : Submodule ℤ (κ → ℝ)) [DiscreteTopology L]
    {A B : Set X} (hA : IsClosed A) (hB : IsClosed B)
    (H : (Y × I) ≃ₜ B)
    (hrim : ∀ z, (H z : X) ∈ A ↔ (z.2 : ℝ) = 0)
    {r : ℝ} (hr : 0 < r)
    (hinj : InjOn (QuotientAddGroup.mk : (κ → ℝ) → (κ → ℝ) ⧸ L.toAddSubgroup)
      (closedBall 0 r))
    (q : C(A,(κ → ℝ) ⧸ L.toAddSubgroup)) (hqi : Function.Injective q)
    (houtside : ∀ x, q x ∉
      (QuotientAddGroup.mk : (κ → ℝ) → (κ → ℝ) ⧸ L.toAddSubgroup) '' ball 0 r)
    (v : C(Y,κ → ℝ)) (hvi : Function.Injective v) (hvn : ∀ y, ‖v y‖ = r)
    (hzero : ∀ y, q ⟨H (y,0),(hrim _).mpr rfl⟩ = QuotientAddGroup.mk (v y)) :
    ∃ F : C(↥(A ∪ B),(κ → ℝ) ⧸ L.toAddSubgroup), Function.Injective F ∧
      (∀ x : A, F ⟨x,Or.inl x.property⟩ = q x) ∧
      ∀ z, F ⟨H z,Or.inr (H z).property⟩ =
        QuotientAddGroup.mk ((1 - (z.2 : ℝ)/2) • v z.1) := by
  obtain ⟨g,hgi,hg0,hgv,hgball⟩ :=
    exists_radial_quotient_collar_embedding L hr hinj v hvi hvn
  let C := A ∪ B
  let a : Set C := Subtype.val ⁻¹' A
  let b : Set C := Subtype.val ⁻¹' B
  let fA : C(a,(κ → ℝ) ⧸ L.toAddSubgroup) :=
    ⟨fun x => q ⟨x.val,x.property⟩,by fun_prop⟩
  let fB : C(b,(κ → ℝ) ⧸ L.toAddSubgroup) :=
    ⟨fun x => g (H.symm ⟨x.val,x.property⟩),by fun_prop⟩
  have hagree (x : C) (hxa : x ∈ a) (hxb : x ∈ b) :
      fA ⟨x,hxa⟩ = fB ⟨x,hxb⟩ := by
    let z := H.symm ⟨x,hxb⟩
    have hzx : (H z : X) = x := congrArg Subtype.val (H.apply_symm_apply _)
    have ht : (z.2 : ℝ) = 0 := (hrim z).mp (hzx.symm ▸ hxa)
    have hz : z = (z.1,0) := Prod.ext rfl (Subtype.ext ht)
    change q ⟨x,hxa⟩ = g z
    rw [hz,hg0,←hzero]
    congr 1
    apply Subtype.ext
    exact hzx.symm.trans (congrArg (fun w => (H w : X)) hz)
  have hcover : a ∪ b = univ := by
    ext x
    exact iff_true_intro x.property
  obtain ⟨F,hFA,hFB⟩ := HamiltonIndexOne.glue_closed_cover a b
    (hA.preimage continuous_subtype_val) (hB.preimage continuous_subtype_val)
    hcover fA fB hagree
  have hFa (x : C) (hx : (x : X) ∈ A) : F x = q ⟨x,hx⟩ := hFA ⟨x,hx⟩
  have hFb (x : C) (hx : (x : X) ∈ B) : F x = g (H.symm ⟨x,hx⟩) := hFB ⟨x,hx⟩
  have hcross (x : A) (z : Y × I) (hh : q x = g z) : (x : X) = H z := by
    have ht : (z.2 : ℝ) = 0 := by
      by_contra hn
      exact houtside x (hh.symm ▸ (hgball z).mpr hn)
    have hz : z = (z.1,0) := Prod.ext rfl (Subtype.ext ht)
    have hq : q x = q ⟨H (z.1,0),(hrim _).mpr rfl⟩ := by
      rw [hzero,←hg0,←hz]
      exact hh
    have hx := congrArg Subtype.val (hqi hq)
    exact hx.trans (congrArg (fun w => (H w : X)) hz).symm
  refine ⟨F,?_,fun x => hFa _ x.property,?_⟩
  · intro x y hh
    apply Subtype.ext
    rcases x.property with hx | hx <;> rcases y.property with hy | hy
    · rw [hFa x hx,hFa y hy] at hh
      exact congrArg (fun z : A => (z : X)) (hqi hh)
    · rw [hFa x hx,hFb y hy] at hh
      exact (hcross ⟨x,hx⟩ _ hh).trans (congrArg Subtype.val (H.apply_symm_apply _))
    · rw [hFb x hx,hFa y hy] at hh
      exact ((hcross ⟨y,hy⟩ _ hh.symm).trans
        (congrArg Subtype.val (H.apply_symm_apply _))).symm
    · rw [hFb x hx,hFb y hy] at hh
      exact congrArg (fun z : B => (z : X)) (H.symm.injective (hgi hh))
  · intro z
    rw [hFb _ (H z).property]
    simpa only [H.symm_apply_apply] using hgv z

theorem exists_closed_annular_end_contraction
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A B : Set X} (hA : IsClosed A) (hB : IsClosed B)
    (H : (Y × I) ≃ₜ B)
    (hrim : ∀ z, (H z : X) ∈ A ↔ (z.2 : ℝ) = 0) :
    ∃ K : C(I × ↥(A ∪ B),↥(A ∪ B)),
      (∀ x, K (0,x) = x) ∧ (∀ x, (K (1,x) : X) ∈ A) ∧
      ∀ (t : I) (x : ↥(A ∪ B)), (x : X) ∈ A → K (t,x) = x := by
  let C := A ∪ B
  let a : Set (I × C) := {z | z.2.val ∈ A}
  let b : Set (I × C) := {z | z.2.val ∈ B}
  let coords : b → Y × I := fun z => H.symm ⟨z.val.2,z.property⟩
  have hcoords : Continuous coords := H.symm.continuous.comp
    ((continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)).subtype_mk _)
  let moved : b → Y × I := fun z => ((coords z).1,
    ⟨(1 - (z.val.1 : ℝ)) * ((coords z).2 : ℝ),
      mul_nonneg (sub_nonneg.mpr z.val.1.property.2) (coords z).2.property.1,
      mul_le_one₀ (by linarith [z.val.1.property.1]) (coords z).2.property.1
        (coords z).2.property.2⟩)
  have hmoved : Continuous moved := by
    apply hcoords.fst.prodMk
    apply Continuous.subtype_mk
    exact (continuous_const.sub (continuous_subtype_val.comp
      (continuous_fst.comp continuous_subtype_val))).mul
        (continuous_subtype_val.comp hcoords.snd)
  let f : C(a,C) := ⟨fun z => z.val.2,by fun_prop⟩
  let g : C(b,C) := ⟨fun z => ⟨H (moved z),Or.inr (H (moved z)).property⟩,
    (continuous_subtype_val.comp (H.continuous.comp hmoved)).subtype_mk _⟩
  have hcoordval (z : b) : (H (coords z) : X) = z.val.2 :=
    congrArg Subtype.val (H.apply_symm_apply _)
  have hagree (z : I × C) (ha : z ∈ a) (hb : z ∈ b) : f ⟨z,ha⟩ = g ⟨z,hb⟩ := by
    have hz : ((coords ⟨z,hb⟩).2 : ℝ) = 0 :=
      (hrim _).mp ((hcoordval ⟨z,hb⟩).symm ▸ ha)
    have hh : moved ⟨z,hb⟩ = coords ⟨z,hb⟩ := by
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        change (1 - (z.1 : ℝ)) * ((coords ⟨z,hb⟩).2 : ℝ) = _
        rw [hz,mul_zero]
    apply Subtype.ext
    change z.2.val = (H (moved ⟨z,hb⟩) : X)
    rw [hh]
    exact (hcoordval ⟨z,hb⟩).symm
  have hcover : a ∪ b = univ := by
    ext z
    exact iff_true_intro z.2.property
  obtain ⟨K,hKa,hKb⟩ := HamiltonIndexOne.glue_closed_cover a b
    (hA.preimage (continuous_subtype_val.comp continuous_snd))
    (hB.preimage (continuous_subtype_val.comp continuous_snd)) hcover f g hagree
  refine ⟨K,?_,?_,?_⟩
  · intro x
    by_cases hx : (x : X) ∈ A
    · exact hKa ⟨(0,x),hx⟩
    · have hb := x.property.resolve_left hx
      rw [hKb ⟨(0,x),hb⟩]
      apply Subtype.ext
      have hh : moved ⟨(0,x),hb⟩ = coords ⟨(0,x),hb⟩ := by
        apply Prod.ext
        · rfl
        · apply Subtype.ext
          simp [moved]
      change (H (moved ⟨(0,x),hb⟩) : X) = x
      rw [hh]
      exact hcoordval _
  · intro x
    by_cases hx : (x : X) ∈ A
    · rw [hKa ⟨(1,x),hx⟩]
      exact hx
    · have hb := x.property.resolve_left hx
      rw [hKb ⟨(1,x),hb⟩]
      apply (hrim _).mpr
      simp [moved]
  · intro t x hx
    exact hKa ⟨(t,x),hx⟩

theorem homotopic_of_closed_annular_end_agreement
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {A B : Set X} (hA : IsClosed A) (hB : IsClosed B)
    (H : (Y × I) ≃ₜ B)
    (hrim : ∀ z, (H z : X) ∈ A ↔ (z.2 : ℝ) = 0)
    (f g : C(↥(A ∪ B),Z))
    (hagree : ∀ x : ↥(A ∪ B), (x : X) ∈ A → f x = g x) :
    f.Homotopic g := by
  obtain ⟨K,h0,h1,_⟩ := exists_closed_annular_end_contraction hA hB H hrim
  let last : C(↥(A ∪ B),↥(A ∪ B)) := K.comp ⟨fun x => (1,x),by fun_prop⟩
  have hf : f.Homotopic (f.comp last) := ⟨{
    toContinuousMap := f.comp K
    map_zero_left := fun x => congrArg f (h0 x)
    map_one_left := fun _ => rfl }⟩
  have hg : g.Homotopic (g.comp last) := ⟨{
    toContinuousMap := g.comp K
    map_zero_left := fun x => congrArg g (h0 x)
    map_one_left := fun _ => rfl }⟩
  have heq : f.comp last = g.comp last := ContinuousMap.ext (fun x => hagree _ (h1 x))
  exact hf.trans (heq ▸ hg.symm)

theorem HamiltonMarkedProtectedBall.exists_closed_annular_end_quotient_embedding_with_lift
    {ι κ α Y : Type*} [Fintype ι] [Fintype κ]
    [TopologicalSpace Y] [ConnectedSpace Y] [Nonempty Y]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) (Fin 3 → ℝ)}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1) :
    let X := LatticeHandleAmbient ι κ L
    let R := latticeHandleDomain ι κ L
    let E := closure (R \ D)
    ∀ {B : Set X}, IsClosed B → B ⊆ E ∩ D →
    ∀ H : (Y × I) ≃ₜ B,
    (∀ z, (H z : X) ∈ frontier R ↔ (z.2 : ℝ) = 0) →
    ∃ a : sphere (0 : ι → ℝ) 1,
      let A := {x : X | x ∈ E ∩ frontier R ∧ x.1 = a.val}
      ∃ F : C(↥(A ∪ B),(κ → ℝ) ⧸ L.toAddSubgroup), Function.Injective F ∧
        (∀ x : A, F ⟨x,Or.inl x.property⟩ = x.val.2) ∧
        (∀ z, F ⟨H z,Or.inr (H z).property⟩ ∈
          (QuotientAddGroup.mk : (κ → ℝ) → (κ → ℝ) ⧸ L.toAddSubgroup) ''
            Metric.ball 0 (3/2) ↔ (z.2 : ℝ) ≠ 0) ∧
        F.Homotopic ⟨fun x => x.val.2,continuous_snd.comp continuous_subtype_val⟩ ∧
        (∀ y, (H (y,0) : X).1 = a.val) ∧
        ∃ v : C(Y,κ → ℝ), Function.Injective v ∧ (∀ y, ‖v y‖ = (3/2 : ℝ)) ∧
          (∀ y, (QuotientAddGroup.mk (v y) : (κ → ℝ) ⧸ L.toAddSubgroup) =
            (H (y,0) : X).2) ∧
          ∀ z, F ⟨H z,Or.inr (H z).property⟩ =
            QuotientAddGroup.mk ((1 - (z.2 : ℝ)/2) • v z.1) := by
  classical
  intro X R E B hB hBE H hHr
  obtain ⟨hu⟩ := Fintype.card_eq_one_iff_nonempty_unique.mp hi
  let : Unique ι := hu
  let S := sphere (0 : ι → ℝ) 1
  have hSf : S.Finite := by
    apply ((Set.finite_singleton (fun _ : ι => (-1 : ℝ))).insert (fun _ : ι => (1 : ℝ))).subset
    intro x hx
    have hc : x = (fun _ => x default) := funext (fun i => congrArg x (Subsingleton.elim i default))
    have hn : |x default| = 1 := by
      have hh := mem_sphere_zero_iff_norm.mp hx
      rwa [hc,pi_norm_const,Real.norm_eq_abs] at hh
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hn with hn | hn
    · exact Or.inl (hc.trans (by rw [hn]))
    · exact Or.inr (hc.trans (by rw [hn]))
  let : Finite S := hSf.to_subtype
  let : DiscreteTopology S := inferInstance
  have hfront (y : Y) : (H (y,0) : X) ∈ frontier R := (hHr _).mpr rfl
  have hfirst (y : Y) : (H (y,0) : X).1 ∈ S := by
    have hh := hfront y
    change (H (y,0) : X) ∈ frontier (closedBall (0 : ι → ℝ) 1 ×ˢ
      (univ : Set ((κ → ℝ) ⧸ L.toAddSubgroup))) at hh
    rw [frontier_prod_univ_eq,frontier_closedBall _ one_ne_zero] at hh
    exact hh.1
  let first : C(Y,S) := ⟨fun y => ⟨(H (y,0) : X).1,hfirst y⟩,
    (continuous_fst.comp (continuous_subtype_val.comp
      (H.continuous.comp (continuous_id.prodMk continuous_const)))).subtype_mk _⟩
  let a := first (Classical.choice ‹Nonempty Y›)
  have ha (y : Y) : first y = a :=
    (isPreconnected_range first.continuous).subsingleton (mem_range_self y)
      (mem_range_self (Classical.choice ‹Nonempty Y›))
  let A := {x : X | x ∈ E ∩ frontier R ∧ x.1 = a.val}
  have hA : IsClosed A := (isClosed_closure.inter isClosed_frontier).inter
    (isClosed_eq continuous_fst continuous_const)
  have hrim (z : Y × I) : (H z : X) ∈ A ↔ (z.2 : ℝ) = 0 := by
    constructor
    · exact fun hz => (hHr z).mp hz.1.2
    · intro hz
      have hh : z = (z.1,0) := Prod.ext rfl (Subtype.ext hz)
      refine ⟨⟨(hBE (H z).property).1,(hHr z).mpr hz⟩,?_⟩
      rw [hh]
      exact congrArg Subtype.val (ha z.1)
  obtain ⟨J,hJ,_,hJrim⟩ := b.exists_attaching_disk_parametrization (by omega)
  have hmark : D ∩ frontier R = hamiltonAttachingBlock ι κ L (3/2) := by
    rcases b.position with ⟨hz,_⟩ | ⟨_,_,_,_,_,hm⟩
    · omega
    · exact hm
  have hend (y : Y) : (H (y,0) : X).2 ∈
      (QuotientAddGroup.mk : (κ → ℝ) → (κ → ℝ) ⧸ L.toAddSubgroup) ''
        closedBall 0 (3/2) := by
    obtain ⟨z,hz,hzx⟩ := hmark.subset ⟨(hBE (H (y,0)).property).2,hfront y⟩
    exact ⟨z.2,hz.2,congrArg Prod.snd hzx⟩
  let v : C(Y,κ → ℝ) := ⟨fun y => J.symm ⟨(H (y,0) : X).2,hend y⟩,
    continuous_subtype_val.comp (J.symm.continuous.comp
      ((continuous_snd.comp (continuous_subtype_val.comp
        (H.continuous.comp (continuous_id.prodMk continuous_const)))).subtype_mk _))⟩
  have hv (y : Y) : (QuotientAddGroup.mk (v y) : (κ → ℝ) ⧸ L.toAddSubgroup) =
      (H (y,0) : X).2 := by
    exact (hJ (J.symm ⟨_,hend y⟩)).symm.trans
      (congrArg Subtype.val (J.apply_symm_apply _))
  have hvi : Function.Injective v := by
    intro y z hh
    have hsecond : (H (y,0) : X).2 = (H (z,0) : X).2 :=
      (hv y).symm.trans ((congrArg QuotientAddGroup.mk hh).trans (hv z))
    have hfirst' := congrArg Subtype.val ((ha y).trans (ha z).symm)
    exact congrArg Prod.fst (H.injective (Subtype.ext (Prod.ext hfirst' hsecond)))
  have hvn (y : Y) : ‖v y‖ = (3/2 : ℝ) := by
    have hle := mem_closedBall_zero_iff.mp (J.symm ⟨_,hend y⟩).property
    change ‖v y‖ ≤ (3/2 : ℝ) at hle
    apply le_antisymm hle
    by_contra hn
    have hh := b.old_exterior_boundary_outside_open_patch he hdim hi
      ⟨(hBE (H (y,0)).property).1,hfront y⟩
    exact hh ⟨v y,mem_ball_zero_iff.mpr (lt_of_not_ge hn),hv y⟩
  let q : C(A,(κ → ℝ) ⧸ L.toAddSubgroup) :=
    ⟨fun x => x.val.2,continuous_snd.comp continuous_subtype_val⟩
  have hqi : Function.Injective q := by
    intro x y hh
    exact Subtype.ext (Prod.ext (x.property.2.trans y.property.2.symm) hh)
  have houtside (x : A) : q x ∉
      (QuotientAddGroup.mk : (κ → ℝ) → (κ → ℝ) ⧸ L.toAddSubgroup) '' Metric.ball 0 (3/2) :=
    b.old_exterior_boundary_outside_open_patch he hdim hi x.property.1
  obtain ⟨F,hFi,hFa,hFb⟩ := exists_closed_annular_end_embedding L hA hB H hrim
    (by norm_num : (0 : ℝ) < 3/2) (b.quotient_injOn_attaching_disk (by omega))
    q hqi houtside v hvi hvn (fun y => (hv y).symm)
  obtain ⟨g,_,_,hgv,hgball⟩ := exists_radial_quotient_collar_embedding L
    (by norm_num : (0 : ℝ) < 3/2) (b.quotient_injOn_attaching_disk (by omega)) v hvi hvn
  refine ⟨a,F,hFi,hFa,?_,?_,?_,v,hvi,hvn,hv,hFb⟩
  · intro z
    rw [hFb,←hgv]
    exact hgball z
  · apply homotopic_of_closed_annular_end_agreement hA hB H hrim
    intro x hx
    exact hFa ⟨x,hx⟩
  · exact fun y => congrArg Subtype.val (ha y)

theorem HamiltonMarkedProtectedBall.exists_closed_annular_end_quotient_embedding
    {ι κ α Y : Type*} [Fintype ι] [Fintype κ]
    [TopologicalSpace Y] [ConnectedSpace Y] [Nonempty Y]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) (Fin 3 → ℝ)}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1) :
    let X := LatticeHandleAmbient ι κ L
    let R := latticeHandleDomain ι κ L
    let E := closure (R \ D)
    ∀ {B : Set X}, IsClosed B → B ⊆ E ∩ D →
    ∀ H : (Y × I) ≃ₜ B,
    (∀ z, (H z : X) ∈ frontier R ↔ (z.2 : ℝ) = 0) →
    ∃ a : sphere (0 : ι → ℝ) 1,
      let A := {x : X | x ∈ E ∩ frontier R ∧ x.1 = a.val}
      ∃ F : C(↥(A ∪ B),(κ → ℝ) ⧸ L.toAddSubgroup), Function.Injective F ∧
        (∀ x : A, F ⟨x,Or.inl x.property⟩ = x.val.2) ∧
        (∀ z, F ⟨H z,Or.inr (H z).property⟩ ∈
          (QuotientAddGroup.mk : (κ → ℝ) → (κ → ℝ) ⧸ L.toAddSubgroup) ''
            Metric.ball 0 (3/2) ↔ (z.2 : ℝ) ≠ 0) ∧
        F.Homotopic ⟨fun x => x.val.2,continuous_snd.comp continuous_subtype_val⟩ := by
  intro X R E B hB hBE H hHr
  obtain ⟨a,F,hFi,hFa,hball,hhom,_⟩ :=
    b.exists_closed_annular_end_quotient_embedding_with_lift he hdim hi hB hBE H hHr
  exact ⟨a,F,hFi,hFa,hball,hhom⟩

end PoincareConjecture.M76
