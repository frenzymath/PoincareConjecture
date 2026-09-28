import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Topology.Compactification.OnePoint.Sphere
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring









set_option autoImplicit false

open Set Metric Topology
open scoped unitInterval

namespace PoincareConjecture.Proofs.M02



theorem exists_cube_closedBall_homeomorph {N : Type*} [Fintype N] :
    ∃ e : (I^N) ≃ₜ closedBall (0 : N → ℝ) 1,
      (∀ t i, (e t : N → ℝ) i = 2 * (t i : ℝ) - 1) ∧
      ∀ t, t ∈ Cube.boundary N ↔ ‖(e t : N → ℝ)‖ = 1 := by
  have hin (t : I^N) : (fun i => 2 * (t i : ℝ) - 1) ∈
      closedBall (0 : N → ℝ) 1 := by
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [(t i).property.1, (t i).property.2]
  have hout (z : closedBall (0 : N → ℝ) 1) (i : N) :
      ((z : N → ℝ) i + 1) / 2 ∈ Icc (0 : ℝ) 1 := by
    have hz : ‖(z : N → ℝ)‖ ≤ 1 := mem_closedBall_zero_iff.mp z.property
    have hi := (norm_le_pi_norm (z : N → ℝ) i).trans hz
    rw [Real.norm_eq_abs, abs_le] at hi
    constructor <;> linarith [hi.1, hi.2]
  let e : (I^N) ≃ₜ closedBall (0 : N → ℝ) 1 := {
    toFun := fun t => ⟨fun i => 2 * (t i : ℝ) - 1, hin t⟩
    invFun := fun z i => ⟨((z : N → ℝ) i + 1) / 2, hout z i⟩
    left_inv := by
      intro t
      funext i
      apply Subtype.ext
      change (2 * (t i : ℝ) - 1 + 1) / 2 = (t i : ℝ)
      ring
    right_inv := by
      intro z
      apply Subtype.ext
      funext i
      change 2 * (((z : N → ℝ) i + 1) / 2) - 1 = (z : N → ℝ) i
      ring
    continuous_toFun := by fun_prop
    continuous_invFun := continuous_pi fun i =>
      ((((continuous_apply i).comp continuous_subtype_val).add
        continuous_const).div_const 2).subtype_mk _ }
  refine ⟨e, fun _ _ => rfl, ?_⟩
  intro t
  have hle : ‖(e t : N → ℝ)‖ ≤ 1 := mem_closedBall_zero_iff.mp (e t).property
  constructor
  · rintro ⟨i, hi⟩
    apply le_antisymm hle
    have hn := norm_le_pi_norm (e t : N → ℝ) i
    change ‖2 * (t i : ℝ) - 1‖ ≤ ‖(e t : N → ℝ)‖ at hn
    rcases hi with hi | hi <;> norm_num [hi] at hn ⊢ <;> exact hn
  · intro hn
    by_contra hboundary
    have hlt : ‖(e t : N → ℝ)‖ < 1 := by
      apply (pi_norm_lt_iff zero_lt_one).mpr
      intro i
      have hzero : (t i : ℝ) ≠ 0 := fun h =>
        hboundary ⟨i, Or.inl (Subtype.ext h)⟩
      have hone : (t i : ℝ) ≠ 1 := fun h =>
        hboundary ⟨i, Or.inr (Subtype.ext h)⟩
      have htzero := lt_of_le_of_ne (t i).property.1 hzero.symm
      have htone := lt_of_le_of_ne (t i).property.2 hone
      change ‖2 * (t i : ℝ) - 1‖ < 1
      rw [Real.norm_eq_abs, abs_lt]
      constructor <;> linarith
    exact (ne_of_lt hlt) hn



theorem exists_onePoint_quotient_of_isOpen
    {K : Type*} [TopologicalSpace K] [T2Space K] [CompactSpace K]
    (U : Set K) (hU : IsOpen U) (hne : Uᶜ.Nonempty) :
    ∃ q : C(K, OnePoint U),
      (∀ u : U, q u = OnePoint.some u) ∧
      (∀ x ∉ U, q x = OnePoint.infty) ∧ IsQuotientMap q ∧
      ∀ x y, q x = q y ↔ x = y ∨ (x ∉ U ∧ y ∉ U) := by
  classical
  let q : K → OnePoint U := fun x =>
    if hx : x ∈ U then OnePoint.some ⟨x, hx⟩ else OnePoint.infty
  have hqin (u : U) : q u = OnePoint.some u := by simp [q, u.property]
  have hqout (x : K) (hx : x ∉ U) : q x = OnePoint.infty := by simp [q, hx]
  have hcontinuous : Continuous q := by
    refine continuous_def.mpr fun V hV => ?_
    by_cases hinfty : OnePoint.infty ∈ V
    · have heq : q ⁻¹' V =
          (Subtype.val '' (((↑) : U → OnePoint U) ⁻¹' V)ᶜ)ᶜ := by
        ext x
        by_cases hx : x ∈ U
        · simp [q, hx]
        · simp [q, hx, hinfty]
      rw [heq]
      exact (((OnePoint.isOpen_def.mp hV).1 hinfty).image
        continuous_subtype_val).isClosed.isOpen_compl
    · have heq : q ⁻¹' V = Subtype.val '' (((↑) : U → OnePoint U) ⁻¹' V) := by
        ext x
        by_cases hx : x ∈ U
        · simp [q, hx]
        · simp [q, hx, hinfty]
      rw [heq]
      exact hU.isOpenMap_subtype_val _ (OnePoint.isOpen_def.mp hV).2
  have hsurjective : Function.Surjective q := by
    intro y
    induction y using OnePoint.rec with
    | infty =>
      obtain ⟨z, hz⟩ := hne
      exact ⟨z, hqout z hz⟩
    | coe u => exact ⟨u, hqin u⟩
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  refine ⟨⟨q, hcontinuous⟩, hqin, hqout,
    IsQuotientMap.of_surjective_continuous hsurjective hcontinuous, ?_⟩
  intro x y
  change q x = q y ↔ _
  by_cases hx : x ∈ U <;> by_cases hy : y ∈ U
  · simp [q, hx, hy]
  · have hxy : x ≠ y := fun h => hy (h ▸ hx)
    simp [q, hx, hy, hxy]
  · have hxy : x ≠ y := fun h => hx (h.symm ▸ hy)
    simp [q, hx, hy, hxy]
  · simp [q, hx, hy]



theorem exists_cube_sphere_quotient_of_card_eq
    {N ι : Type*} [Fintype N] [Nonempty N] [Fintype ι]
    (hdim : Fintype.card N + 1 = Fintype.card ι) :
    ∃ q : C(I^N, sphere (0 : EuclideanSpace ℝ ι) 1),
      IsQuotientMap q ∧
      ∀ x y, q x = q y ↔ x = y ∨
        (x ∈ Cube.boundary N ∧ y ∈ Cube.boundary N) := by
  let E := N → ℝ
  obtain ⟨e, _, he⟩ := exists_cube_closedBall_homeomorph (N := N)
  let U : Set (closedBall (0 : E) 1) := {z | (z : E) ∈ ball 0 1}
  have hU : IsOpen U := isOpen_ball.preimage continuous_subtype_val
  have hboundary (t : I^N) : e t ∉ U ↔ t ∈ Cube.boundary N := by
    have hle : ‖(e t : E)‖ ≤ 1 := mem_closedBall_zero_iff.mp (e t).property
    change ¬ (e t : E) ∈ ball 0 1 ↔ _
    rw [mem_ball_zero_iff, not_lt, he t]
    exact ⟨fun h => le_antisymm hle h, fun h => h.ge⟩
  have hnonempty : Uᶜ.Nonempty := by
    refine ⟨e (fun _ => 0), (hboundary _).mpr ?_⟩
    exact ⟨Classical.choice (inferInstance : Nonempty N), Or.inl rfl⟩
  obtain ⟨q, _, _, hq, hfibers⟩ := exists_onePoint_quotient_of_isOpen U hU hnonempty
  let eU : U ≃ₜ ball (0 : E) 1 := {
    toFun := fun z => ⟨z.val.val, z.property⟩
    invFun := fun z => ⟨⟨z.val, ball_subset_closedBall z.property⟩, z.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  let eE : U ≃ₜ E := eU.trans (Homeomorph.unitBall (E := E)).symm
  let eS : OnePoint U ≃ₜ sphere (0 : EuclideanSpace ℝ ι) 1 :=
    eE.onePointCongr.trans
      (onePointEquivSphereOfFinrankEq (V := E) (by simpa [E] using hdim))
  let Q : C(I^N, sphere (0 : EuclideanSpace ℝ ι) 1) :=
    ⟨fun t => eS (q (e t)), eS.continuous.comp (q.continuous.comp e.continuous)⟩
  refine ⟨Q, IsQuotientMap.of_surjective_continuous
    (eS.surjective.comp (hq.surjective.comp e.surjective)) Q.continuous, ?_⟩
  intro x y
  change eS (q (e x)) = eS (q (e y)) ↔ _
  rw [eS.injective.eq_iff, hfibers, e.injective.eq_iff, hboundary, hboundary]



theorem exists_sphere_genLoopEquiv
    {N ι X : Type*} [Fintype N] [Nonempty N] [Fintype ι]
    [TopologicalSpace X]
    (hdim : Fintype.card N + 1 = Fintype.card ι) (x : X) :
    ∃ (q : C(I^N, sphere (0 : EuclideanSpace ℝ ι) 1))
      (b : sphere (0 : EuclideanSpace ℝ ι) 1),
      IsQuotientMap q ∧
      (∀ t, q t = b ↔ t ∈ Cube.boundary N) ∧
      ∃ e : {f : C(sphere (0 : EuclideanSpace ℝ ι) 1, X) // f b = x} ≃
          GenLoop N X x,
        (∀ f, (e f).val = f.val.comp q) ∧
        ∀ f g, GenLoop.Homotopic (e f) (e g) ↔
          f.val.HomotopicRel g.val {b} := by
  obtain ⟨q, hq, hfibers⟩ := exists_cube_sphere_quotient_of_card_eq hdim
  let z : I^N := fun _ => 0
  have hz : z ∈ Cube.boundary N :=
    ⟨Classical.choice (inferInstance : Nonempty N), Or.inl rfl⟩
  let b := q z
  have hboundary (t : I^N) : q t = b ↔ t ∈ Cube.boundary N := by
    change q t = q z ↔ _
    rw [hfibers]
    exact ⟨fun h => h.elim (fun htz => htz ▸ hz) And.left,
      fun ht => Or.inr ⟨ht, hz⟩⟩
  let toLoop : {f : C(sphere (0 : EuclideanSpace ℝ ι) 1, X) // f b = x} →
      GenLoop N X x := fun f => ⟨f.val.comp q, by
        intro t ht
        change f.val (q t) = x
        rw [(hboundary t).mpr ht]
        exact f.property⟩
  have hfactor (p : GenLoop N X x) : Function.FactorsThrough p.val q := by
    intro a c hac
    rcases (hfibers a c).mp hac with h | ⟨ha, hc⟩
    · exact congrArg p h
    · exact (GenLoop.boundary p a ha).trans (GenLoop.boundary p c hc).symm
  let fromLoop : GenLoop N X x →
      {f : C(sphere (0 : EuclideanSpace ℝ ι) 1, X) // f b = x} := fun p =>
    ⟨hq.lift p.val (hfactor p), by
      have hp := ContinuousMap.congr_fun (hq.lift_comp p.val (hfactor p)) z
      exact hp.trans (GenLoop.boundary p z hz)⟩
  have hfrom (p : GenLoop N X x) (t : I^N) : (fromLoop p).val (q t) = p t :=
    ContinuousMap.congr_fun (hq.lift_comp p.val (hfactor p)) t
  let e : {f : C(sphere (0 : EuclideanSpace ℝ ι) 1, X) // f b = x} ≃
      GenLoop N X x := {
    toFun := toLoop
    invFun := fromLoop
    left_inv := by
      intro f
      apply Subtype.ext
      ext s
      obtain ⟨t, rfl⟩ := hq.surjective s
      exact hfrom (toLoop f) t
    right_inv := by
      intro p
      apply GenLoop.ext
      intro t
      exact hfrom p t }
  refine ⟨q, b, hq, hboundary, e, fun _ => rfl, ?_⟩
  intro f g
  constructor
  · rintro ⟨H⟩
    let Hc : C(I^N, C(unitInterval, X)) :=
      (H.toHomotopy.toContinuousMap.comp ⟨Prod.swap, continuous_swap⟩).curry
    have hHfactor : Function.FactorsThrough Hc q := by
      intro a c hac
      rcases (hfibers a c).mp hac with hac | ⟨ha, hc⟩
      · rw [hac]
      · ext t
        change H (t, a) = H (t, c)
        rw [H.eq_fst t ha, H.eq_fst t hc]
        exact (GenLoop.boundary (e f) a ha).trans (GenLoop.boundary (e f) c hc).symm
    let F := hq.lift Hc hHfactor
    have hF (t : I^N) : F (q t) = Hc t :=
      ContinuousMap.congr_fun (hq.lift_comp Hc hHfactor) t
    refine ⟨{
      toFun := fun p => F p.2 p.1
      continuous_toFun := (F.continuous.comp continuous_snd).eval continuous_fst
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }⟩
    · intro s
      obtain ⟨t, rfl⟩ := hq.surjective s
      change F (q t) 0 = f.val (q t)
      rw [hF]
      exact H.apply_zero t
    · intro s
      obtain ⟨t, rfl⟩ := hq.surjective s
      change F (q t) 1 = g.val (q t)
      rw [hF]
      exact H.apply_one t
    · intro t s hs
      have hsb : s = b := hs
      subst s
      change F (q z) t = f.val (q z)
      rw [hF]
      exact H.eq_fst t hz
  · rintro ⟨H⟩
    refine ⟨{
      toFun := fun p => H (p.1, q p.2)
      continuous_toFun := H.continuous.comp
        (continuous_fst.prodMk (q.continuous.comp continuous_snd))
      map_zero_left := fun t => H.apply_zero (q t)
      map_one_left := fun t => H.apply_one (q t)
      prop' := ?_ }⟩
    intro t a ha
    change H (t, q a) = f.val (q a)
    exact H.eq_fst t ((hboundary a).mpr ha)

end PoincareConjecture.Proofs.M02
