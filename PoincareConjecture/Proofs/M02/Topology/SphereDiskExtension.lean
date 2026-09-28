import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Compactification.OnePoint.Sphere

set_option autoImplicit false

open Set Metric
open scoped Topology unitInterval

universe u v

namespace PoincareConjecture.Proofs.M02.Topology

noncomputable section

theorem exists_cube_ball_coordinates (n : Nat) :
    ∃ e : (Fin n → unitInterval) ≃ₜ closedBall (0 : Fin n → ℝ) 1,
      ∀ t, t ∈ Cube.boundary (Fin n) ↔ ‖(e t : Fin n → ℝ)‖ = 1 := by
  let a (t : Fin n → unitInterval) : Fin n → ℝ := fun i => 2 * (t i : ℝ) - 1
  have ha (t : Fin n → unitInterval) : a t ∈ closedBall 0 1 := by
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> dsimp [a] <;> linarith [(t i).property.1, (t i).property.2]
  have hb (z : closedBall (0 : Fin n → ℝ) 1) (i : Fin n) :
      ((z.val i + 1) / 2) ∈ Icc (0 : ℝ) 1 := by
    have hzi := (norm_le_pi_norm z.val i).trans (mem_closedBall_zero_iff.mp z.property)
    rw [Real.norm_eq_abs, abs_le] at hzi
    constructor <;> linarith [hzi.1, hzi.2]
  let e : (Fin n → unitInterval) ≃ₜ closedBall (0 : Fin n → ℝ) 1 :=
    { toFun := fun t => ⟨a t, ha t⟩
      invFun := fun z i => ⟨(z.val i + 1) / 2, hb z i⟩
      left_inv := by intro t; funext i; apply Subtype.ext; dsimp [a]; ring
      right_inv := by intro z; apply Subtype.ext; funext i; dsimp [a]; ring
      continuous_toFun := by fun_prop
      continuous_invFun := continuous_pi fun i =>
        ((((continuous_apply i).comp continuous_subtype_val).add
          continuous_const).div_const 2).subtype_mk _ }
  refine ⟨e, fun t => ?_⟩
  have hle : ‖(e t : Fin n → ℝ)‖ ≤ 1 := mem_closedBall_zero_iff.mp (e t).property
  constructor
  · rintro ⟨i, hi | hi⟩ <;> apply le_antisymm hle
    · have h := norm_le_pi_norm (e t : Fin n → ℝ) i
      change ‖2 * (t i : ℝ) - 1‖ ≤ _ at h
      simpa [hi] using h
    · have h := norm_le_pi_norm (e t : Fin n → ℝ) i
      change ‖2 * (t i : ℝ) - 1‖ ≤ _ at h
      norm_num [hi] at h ⊢
      exact h
  · intro hnorm
    by_contra h
    have hlt : ‖(e t : Fin n → ℝ)‖ < 1 := by
      rw [pi_norm_lt_iff zero_lt_one]
      intro i
      have h0 : (t i : ℝ) ≠ 0 := fun hi => h ⟨i, Or.inl (Subtype.ext hi)⟩
      have h1 : (t i : ℝ) ≠ 1 := fun hi => h ⟨i, Or.inr (Subtype.ext hi)⟩
      change ‖2 * (t i : ℝ) - 1‖ < 1
      rw [Real.norm_eq_abs, abs_lt]
      constructor <;> linarith [lt_of_le_of_ne (t i).property.1 h0.symm,
        lt_of_le_of_ne (t i).property.2 h1]
    exact hlt.ne hnorm

theorem exists_open_complement_quotient
    {K : Type u} [TopologicalSpace K] [T2Space K] [CompactSpace K]
    (U : Set K) (hU : IsOpen U) (hne : Uᶜ.Nonempty) :
    ∃ q : C(K, OnePoint U), _root_.Topology.IsQuotientMap q ∧
      ∀ a b, q a = q b ↔ a = b ∨ (a ∉ U ∧ b ∉ U) := by
  classical
  let q (x : K) : OnePoint U := if h : x ∈ U then (⟨x, h⟩ : U) else OnePoint.infty
  have hcont : Continuous q := by
    apply continuous_def.mpr
    intro V hV
    by_cases hv : OnePoint.infty ∈ V
    · have heq : q ⁻¹' V = (Subtype.val '' (((↑) : U → OnePoint U) ⁻¹' V)ᶜ)ᶜ := by
        ext x
        by_cases hx : x ∈ U <;> simp [q, hx, hv]
      rw [heq]
      exact (((OnePoint.isOpen_def.mp hV).1 hv).image continuous_subtype_val).isClosed.isOpen_compl
    · have heq : q ⁻¹' V = Subtype.val '' (((↑) : U → OnePoint U) ⁻¹' V) := by
        ext x
        by_cases hx : x ∈ U <;> simp [q, hx, hv]
      rw [heq]
      exact hU.isOpenMap_subtype_val _ (OnePoint.isOpen_def.mp hV).2
  have hsurj : Function.Surjective q := by
    intro z
    induction z using OnePoint.rec with
    | infty => obtain ⟨x, hx⟩ := hne; exact ⟨x, by simp [q, show x ∉ U from hx]⟩
    | coe x => exact ⟨x.val, by simp [q, x.property]⟩
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  refine ⟨⟨q, hcont⟩, .of_surjective_continuous hsurj hcont, ?_⟩
  intro a b
  by_cases ha : a ∈ U <;> by_cases hb : b ∈ U
  · simp [q, ha, hb]
  · have hab : a ≠ b := fun h => hb (h ▸ ha)
    simp [q, ha, hb, hab]
  · have hab : a ≠ b := fun h => ha (h.symm ▸ hb)
    simp [q, ha, hb, hab]
  · simp [q, ha, hb]

theorem exists_cube_boundary_sphere_quotient (n : Nat) :
    ∃ q : C((Fin (n + 1) → unitInterval),
        sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1),
      _root_.Topology.IsQuotientMap q ∧
      ∀ a b, q a = q b ↔ a = b ∨
        (a ∈ Cube.boundary (Fin (n + 1)) ∧ b ∈ Cube.boundary (Fin (n + 1))) := by
  let E := Fin (n + 1) → ℝ
  obtain ⟨e, he⟩ := exists_cube_ball_coordinates (n + 1)
  let U : Set (closedBall (0 : E) 1) := {z | (z : E) ∈ ball 0 1}
  have hU : IsOpen U := isOpen_ball.preimage continuous_subtype_val
  have hboundary (t : Fin (n + 1) → unitInterval) : e t ∉ U ↔ t ∈ Cube.boundary _ := by
    change ¬ (e t : E) ∈ ball 0 1 ↔ _
    rw [mem_ball_zero_iff]
    rw [not_lt, he t]
    exact ⟨fun h => le_antisymm (mem_closedBall_zero_iff.mp (e t).property) h,
      fun h => h.ge⟩
  have hne : Uᶜ.Nonempty :=
    ⟨e (fun _ => 0), (hboundary _).mpr ⟨0, Or.inl rfl⟩⟩
  obtain ⟨q, hq, hfiber⟩ := exists_open_complement_quotient U hU hne
  let hball : U ≃ₜ ball (0 : E) 1 :=
    { toFun := fun z => ⟨z.val.val, z.property⟩
      invFun := fun z => ⟨⟨z.val, ball_subset_closedBall z.property⟩, z.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let hspace : U ≃ₜ E := hball.trans (Homeomorph.unitBall (E := E)).symm
  let hsphere : OnePoint U ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1 :=
    hspace.onePointCongr.trans (onePointEquivSphereOfFinrankEq (by simp [E]))
  let Q : C((Fin (n + 1) → unitInterval),
      sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1) :=
    (hsphere : C(_, _)).comp (q.comp (e : C(_, _)))
  refine ⟨Q, .of_surjective_continuous
    (hsphere.surjective.comp (hq.surjective.comp e.surjective)) Q.continuous, ?_⟩
  intro a b
  change hsphere (q (e a)) = hsphere (q (e b)) ↔ _
  rw [hsphere.injective.eq_iff, hfiber, e.injective.eq_iff, hboundary, hboundary]

theorem sphere_map_nullhomotopic_of_pi_trivial
    {Y : Type v} [TopologicalSpace Y] (n : Nat)
    (hpi : ∀ y : Y, Subsingleton (HomotopyGroup.Pi (n + 1) Y y))
    (f : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, Y)) :
    f.Nullhomotopic := by
  obtain ⟨q, hq, hfiber⟩ := exists_cube_boundary_sphere_quotient n
  let zero : Fin (n + 1) → unitInterval := fun _ => 0
  have hz : zero ∈ Cube.boundary (Fin (n + 1)) := ⟨0, Or.inl rfl⟩
  let y := f (q zero)
  let p : GenLoop (Fin (n + 1)) Y y :=
    ⟨f.comp q, fun z h => congrArg f ((hfiber z zero).mpr (Or.inr ⟨h, hz⟩))⟩
  obtain ⟨H⟩ : GenLoop.Homotopic p (GenLoop.const : GenLoop (Fin (n + 1)) Y y) :=
    Quotient.exact ((hpi y).elim (⟦p⟧ : HomotopyGroup.Pi (n + 1) Y y) ⟦GenLoop.const⟧)
  let Q : C(unitInterval × (Fin (n + 1) → unitInterval),
      unitInterval × sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1) :=
    ⟨fun z => (z.1, q z.2), continuous_fst.prodMk (q.continuous.comp continuous_snd)⟩
  have hQ : _root_.Topology.IsQuotientMap Q := by
    apply _root_.Topology.IsQuotientMap.of_surjective_continuous _ Q.continuous
    rintro ⟨t, x⟩
    obtain ⟨z, rfl⟩ := hq.surjective x
    exact ⟨(t, z), rfl⟩
  have hfactor : Function.FactorsThrough H.toHomotopy.toContinuousMap Q := by
    rintro ⟨t, a⟩ ⟨s, b⟩ h
    have htime : t = s := congrArg Prod.fst h
    have hab : q a = q b := congrArg Prod.snd h
    subst s
    rcases (hfiber a b).mp hab with rfl | ⟨ha, hb⟩
    · rfl
    · exact (H.eq_fst t ha).trans ((GenLoop.boundary p a ha).trans
        ((GenLoop.boundary p b hb).symm.trans (H.eq_fst t hb).symm))
  let G := hQ.lift H.toHomotopy.toContinuousMap hfactor
  have hG (t : unitInterval) (a : Fin (n + 1) → unitInterval) : G (t, q a) = H (t, a) :=
    DFunLike.congr_fun (hQ.lift_comp H.toHomotopy.toContinuousMap hfactor) (t, a)
  refine ⟨y, ⟨{ toContinuousMap := G, map_zero_left := ?_, map_one_left := ?_ }⟩⟩
  · intro x
    obtain ⟨a, rfl⟩ := hq.surjective x
    exact (hG 0 a).trans (H.apply_zero a)
  · intro x
    obtain ⟨a, rfl⟩ := hq.surjective x
    exact (hG 1 a).trans (H.apply_one a)

def unitSphereHomeomorph
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃L[ℝ] F) : sphere (0 : E) 1 ≃ₜ sphere (0 : F) 1 := by
  have hn (x : sphere (0 : E) 1) : ‖e x‖ ≠ 0 := by
    rw [norm_ne_zero_iff, ne_eq, e.map_eq_zero_iff]
    exact ne_zero_of_mem_sphere one_ne_zero x
  have hm (x : sphere (0 : F) 1) : ‖e.symm x‖ ≠ 0 := by
    rw [norm_ne_zero_iff, ne_eq, e.symm.map_eq_zero_iff]
    exact ne_zero_of_mem_sphere one_ne_zero x
  refine
    { toFun := fun x => ⟨‖e x‖⁻¹ • e x, ?_⟩
      invFun := fun x => ⟨‖e.symm x‖⁻¹ • e.symm x, ?_⟩
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · simp [norm_smul, hn x]
  · simp [norm_smul, hm x]
  · intro x
    apply Subtype.ext
    simp [map_smul, norm_smul, smul_smul, mem_sphere_zero_iff_norm.mp x.property, hn x]
  · intro x
    apply Subtype.ext
    simp [map_smul, norm_smul, smul_smul, mem_sphere_zero_iff_norm.mp x.property, hm x]
  · apply Continuous.subtype_mk
    exact ((e.continuous.comp continuous_subtype_val).norm.inv₀ hn).smul
      (e.continuous.comp continuous_subtype_val)
  · apply Continuous.subtype_mk
    exact ((e.symm.continuous.comp continuous_subtype_val).norm.inv₀ hm).smul
      (e.symm.continuous.comp continuous_subtype_val)

theorem exists_disk_extension_of_nullhomotopic
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    {Y : Type v} [TopologicalSpace Y]
    (f : C(sphere (0 : E) 1, Y)) (hf : f.Nullhomotopic) :
    ∃ F : C(closedBall (0 : E) 1, Y),
      ∀ x : sphere (0 : E) 1, F ⟨x.val, sphere_subset_closedBall x.property⟩ = f x := by
  obtain ⟨y, ⟨H⟩⟩ := hf
  let Q : C(unitInterval × sphere (0 : E) 1, closedBall (0 : E) 1) :=
    ⟨fun z => ⟨(z.1 : ℝ) • z.2.val, by
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_nonneg z.1.property.1,
        mem_sphere_zero_iff_norm.mp z.2.property, mul_one]
      exact z.1.property.2⟩, by fun_prop⟩
  have hnorm (z : unitInterval × sphere (0 : E) 1) : ‖(Q z : E)‖ = z.1 := by
    simp only [Q, ContinuousMap.coe_mk, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg z.1.property.1, mem_sphere_zero_iff_norm.mp z.2.property, mul_one]
  have hsurj : Function.Surjective Q := by
    intro z
    by_cases hz : (z : E) = 0
    · obtain ⟨x, hx⟩ := NormedSpace.sphere_nonempty (E := E).mpr zero_le_one
      refine ⟨(0, ⟨x, hx⟩), Subtype.ext ?_⟩
      simpa [Q] using hz.symm
    · have hn : ‖(z : E)‖ ≠ 0 := norm_ne_zero_iff.mpr hz
      let t : unitInterval := ⟨‖(z : E)‖, norm_nonneg _, mem_closedBall_zero_iff.mp z.property⟩
      let x : sphere (0 : E) 1 := ⟨‖(z : E)‖⁻¹ • z.val, by
        simp [norm_smul, hn]⟩
      refine ⟨(t, x), Subtype.ext ?_⟩
      simp [Q, t, x, smul_smul, hn]
  have hQ : _root_.Topology.IsQuotientMap Q :=
    .of_surjective_continuous hsurj Q.continuous
  have hfactor : Function.FactorsThrough H.symm.toContinuousMap Q := by
    rintro ⟨t, a⟩ ⟨s, b⟩ hab
    have htime : t = s := Subtype.ext
      ((hnorm (t, a)).symm.trans ((congrArg (fun z : closedBall (0 : E) 1 => ‖z.val‖) hab).trans
        (hnorm (s, b))))
    subst s
    by_cases ht : (t : ℝ) = 0
    · have ht' : t = 0 := Subtype.ext ht
      subst t
      exact (H.symm.apply_zero a).trans (H.symm.apply_zero b).symm
    · have hsmul : (t : ℝ) • a.val = (t : ℝ) • b.val := congrArg Subtype.val hab
      have heq : a = b := Subtype.ext ((smul_right_injective E ht) hsmul)
      subst b
      rfl
  let F := hQ.lift H.symm.toContinuousMap hfactor
  refine ⟨F, fun x => ?_⟩
  have h := DFunLike.congr_fun (hQ.lift_comp H.symm.toContinuousMap hfactor) (1, x)
  change F (Q (1, x)) = H.symm (1, x) at h
  have hx : Q (1, x) = ⟨x.val, sphere_subset_closedBall x.property⟩ :=
    Subtype.ext (by simp [Q])
  rw [hx] at h
  exact h.trans (H.symm.apply_one x)

theorem exists_characteristic_disk_extension
    {Y : Type v} [TopologicalSpace Y] (n : Nat)
    (hpi : ∀ y : Y, Subsingleton (HomotopyGroup.Pi (n + 1) Y y))
    (f : C(sphere (0 : Fin (n + 2) → ℝ) 1, Y)) :
    ∃ F : C(closedBall (0 : Fin (n + 2) → ℝ) 1, Y),
      ∀ x : sphere (0 : Fin (n + 2) → ℝ) 1,
        F ⟨x.val, sphere_subset_closedBall x.property⟩ = f x := by
  let e : sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1 ≃ₜ
      sphere (0 : Fin (n + 2) → ℝ) 1 := unitSphereHomeomorph
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n + 2) => ℝ))
  have hf := sphere_map_nullhomotopic_of_pi_trivial n hpi (f.comp (e : C(_, _)))
  let einv : C(sphere (0 : Fin (n + 2) → ℝ) 1,
      sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1) := ⟨e.symm, e.symm.continuous⟩
  have h := hf.comp_left einv
  have heq : (f.comp (e : C(_, _))).comp einv = f := by
    ext x
    exact congrArg f (e.apply_symm_apply x)
  rw [heq] at h
  exact exists_disk_extension_of_nullhomotopic f h

end

end PoincareConjecture.Proofs.M02.Topology
