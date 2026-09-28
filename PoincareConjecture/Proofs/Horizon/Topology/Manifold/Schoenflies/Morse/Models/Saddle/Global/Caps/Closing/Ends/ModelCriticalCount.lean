import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.ModelCritical
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.ModelCenter
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.CriticalPoints
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Nested.CriticalLevels.Cardinality

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

private theorem standard_critical_points_card_bound :
    Finite {q : S2 | mfderiv (𝓡 2) 𝓘(Real, Real) Saddle.height q = 0} ∧
    Nat.card {q : S2 | mfderiv (𝓡 2) 𝓘(Real, Real) Saddle.height q = 0} ≤ 4 := by
  classical
  let A : Finset E3 := {Saddle.vector 0 0 1, Saddle.vector 0 0 (-1),
    Saddle.vector (Real.sqrt (3/4)) 0 (-1/2),
    Saddle.vector (-Real.sqrt (3/4)) 0 (-1/2)}
  have hmem (q : S2) (hq : mfderiv (𝓡 2) 𝓘(Real, Real) Saddle.height q = 0) :
      (q : E3) ∈ A := by
    obtain ⟨hy, hx | hz⟩ := (Saddle.height_critical_iff q).mp hq
    · have hn := EuclideanSpace.norm_sq_eq (q : E3)
      simp [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs, hx, hy] at hn
      have hz : (q : E3) 2 = 1 ∨ (q : E3) 2 = -1 := by
        apply sq_eq_one_iff.mp
        nlinarith
      rcases hz with hz | hz
      · have he : (q : E3) = Saddle.vector 0 0 1 := by
          ext j
          fin_cases j <;> simp [hx, hy, hz]
        simp [he, A]
      · have he : (q : E3) = Saddle.vector 0 0 (-1) := by
          ext j
          fin_cases j <;> simp [hx, hy, hz]
        simp [he, A]
    · have hn := EuclideanSpace.norm_sq_eq (q : E3)
      simp [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs, hy, hz] at hn
      have hsq : ((q : E3) 0)^2 = (Real.sqrt (3/4))^2 := by
        rw [Real.sq_sqrt (by norm_num : (0 : Real) ≤ 3/4)]
        nlinarith
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hx | hx
      · have he : (q : E3) = Saddle.vector (Real.sqrt (3/4)) 0 (-1/2) := by
          ext j
          fin_cases j <;> simp [hx, hy, hz]
        simp [he, A]
      · have he : (q : E3) = Saddle.vector (-Real.sqrt (3/4)) 0 (-1/2) := by
          ext j
          fin_cases j <;> simp [hx, hy, hz]
        simp [he, A]
  let j : {q : S2 | mfderiv (𝓡 2) 𝓘(Real, Real) Saddle.height q = 0} → ↑A :=
    fun q => ⟨q.val, hmem q.val q.property⟩
  have hj : Injective j := by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ↑A => (z : E3)) he
  refine ⟨Finite.of_injective j hj, ?_⟩
  calc
    _ ≤ Nat.card ↑A := Nat.card_le_card_of_injective j hj
    _ = A.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ 4 := by
      dsimp [A]
      exact le_trans (Finset.card_insert_le _ _) (by
        have h1 := Finset.card_insert_le (Saddle.vector (0 : Real) 0 (-1))
          {Saddle.vector (Real.sqrt (3/4)) 0 (-1/2),
            Saddle.vector (-Real.sqrt (3/4)) 0 (-1/2)}
        have h2 := Finset.card_le_two
          (a := Saddle.vector (Real.sqrt (3/4)) 0 (-1/2))
          (b := Saddle.vector (-Real.sqrt (3/4)) 0 (-1/2))
        omega)

open SaddleLevel

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

theorem terminal_model_critical_iff
    (data : TerminalSaddleData M P p e) (q : S2) :
    mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun y : S2 => inner Real (M.v : E3)
        (data.toTerminalSaddleGeometry.filledModel y)) q = 0 ↔
    mfderiv (𝓡 2) 𝓘(Real, Real) (fun y : S2 => data.model y 2) q = 0 := by
  let h : S2 → Real := fun y => data.model y 2
  have hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h :=
    (EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3)).contMDiff.comp
      (data.model.contMDiff.comp contMDiff_coe_sphere)
  have heq : (fun y : S2 => inner Real (M.v : E3)
      (data.toTerminalSaddleGeometry.filledModel y)) =
      (fun _ : S2 => inner Real (M.v : E3) (g p)) +
        data.scale • (h - fun _ => data.model (data.modelChart 0) 2) := by
    funext y
    exact data.transport_height (data.model y)
  have hd := hh.mdifferentiable (by simp) q
  rw [heq, mfderiv_add mdifferentiableAt_const
    ((hd.sub mdifferentiableAt_const).const_smul data.scale),
    mfderiv_const, zero_add, const_smul_mfderiv (hd.sub mdifferentiableAt_const),
    mfderiv_sub hd mdifferentiableAt_const, mfderiv_const, sub_zero]
  exact smul_eq_zero.trans (or_iff_right (ne_of_gt data.scale_pos))

theorem finite_terminal_model_critical_points
    (data : TerminalSaddleData M P p e) :
    Finite {q : S2 | mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun y : S2 => inner Real (M.v : E3)
        (data.toTerminalSaddleGeometry.filledModel y)) q = 0} ∧
    Nat.card {q : S2 | mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun y : S2 => inner Real (M.v : E3)
        (data.toTerminalSaddleGeometry.filledModel y)) q = 0} ≤ 4 := by
  have heq := Set.ext (terminal_model_critical_iff data)
  rw [heq]
  rcases data.model_kind with hstd | hnest
  · rw [hstd]
    exact standard_critical_points_card_bound
  · rw [hnest]
    exact ⟨Saddle.Nested.finite_critical_points.to_subtype,
      Saddle.Nested.card_critical_points_le_four⟩

private theorem existsUnique_critical_in_cap_of_central_point
    (data : TerminalSaddleData M P p e) (i : Fin 3)
    {q₀ : S2}
    (h₀ : inner Real (M.v : E3) (data.toTerminalSaddleGeometry.filledModel q₀) ∈
      Ioo data.ends.lowerCut data.ends.upperCut)
    (hc₀ : mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun y : S2 => inner Real (M.v : E3)
        (data.toTerminalSaddleGeometry.filledModel y)) q₀ = 0) :
    ∃! q : S2, q ∈ data.toTerminalSaddleGeometry.modelDomain i ∧
      mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun y : S2 => inner Real (M.v : E3)
          (data.toTerminalSaddleGeometry.filledModel y)) q = 0 := by
  classical
  let h : S2 → Real := fun y => inner Real (M.v : E3)
    (data.toTerminalSaddleGeometry.filledModel y)
  let Z := {q : S2 | mfderiv (𝓡 2) 𝓘(Real, Real) h q = 0}
  have hh : Continuous h :=
    (innerSL Real (M.v : E3)).continuous.comp
      (data.toTerminalSaddleGeometry.filledModel.contMDiff.continuous.comp continuous_subtype_val)
  have hdis (j k : Fin 3) (hjk : j ≠ k) :
      Disjoint (data.toTerminalSaddleGeometry.modelDomain j)
        (data.toTerminalSaddleGeometry.modelDomain k) := by
    apply disjoint_left.mpr
    intro y hyj hyk
    exact disjoint_left.mp (data.model_disjoint hjk) ⟨y, hyj, rfl⟩ ⟨y, hyk, rfl⟩
  have hnot (j : Fin 3) : q₀ ∉ data.toTerminalSaddleGeometry.modelDomain j := by
    have hsub : data.toTerminalSaddleGeometry.modelDomain j ⊆
        {y : S2 | h y ∉ Ioo data.ends.lowerCut data.ends.upperCut} := by
      apply closure_minimal _ (isOpen_Ioo.preimage hh).isClosed_compl
      intro y hy hiy
      exact connectedComponentIn_subset _ _ hy ⟨hiy.1.le, hiy.2.le⟩
    exact fun hq => hsub hq h₀
  choose q hqK hqout hqc using exists_critical_in_terminal_model_cap data
  let J : Option (Fin 3) → Z
    | none => ⟨q₀, hc₀⟩
    | some j => ⟨q j, hqc j⟩
  have hJ : Injective J := by
    intro a b hab
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some k =>
        have he : q₀ = q k := congrArg Subtype.val hab
        exact (hnot k (he ▸ hqK k)).elim
    | some j =>
      cases b with
      | none =>
        have he : q j = q₀ := congrArg Subtype.val hab
        exact (hnot j (he ▸ hqK j)).elim
      | some k =>
        have he : q j = q k := congrArg Subtype.val hab
        by_cases hjk : j = k
        · exact congrArg some hjk
        · exact (disjoint_left.mp (hdis j k hjk) (hqK j) (he ▸ hqK k)).elim
  have hfinite : Finite Z := (finite_terminal_model_critical_points data).1
  let : Finite Z := hfinite
  let : Fintype Z := Fintype.ofFinite Z
  have hcard : Fintype.card Z ≤ 4 := by
    simpa only [Nat.card_eq_fintype_card] using
      (finite_terminal_model_critical_points data).2
  have hsurj : Surjective J :=
    ((Fintype.bijective_iff_injective_and_card J).mpr ⟨hJ, by
      have hle := Fintype.card_le_of_injective J hJ
      simp only [Fintype.card_option, Fintype.card_fin] at hle ⊢
      omega⟩).2
  refine ⟨q i, ⟨hqK i, hqc i⟩, ?_⟩
  intro y hy
  obtain ⟨a, ha⟩ := hsurj ⟨y, hy.2⟩
  cases a with
  | none =>
    have he : q₀ = y := congrArg Subtype.val ha
    exact (hnot i (he ▸ hy.1)).elim
  | some j =>
    have he : q j = y := congrArg Subtype.val ha
    by_cases hji : j = i
    · simpa only [hji] using he.symm
    · exact (disjoint_left.mp (hdis j i hji) (hqK j) (he ▸ hy.1)).elim

theorem existsUnique_critical_in_terminal_model_cap
    (data : TerminalSaddleData M P p e) (i : Fin 3) :
    ∃! q : S2, q ∈ data.toTerminalSaddleGeometry.modelDomain i ∧
      mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun y : S2 => inner Real (M.v : E3)
          (data.toTerminalSaddleGeometry.filledModel y)) q = 0 := by
  obtain ⟨q₀, h₀, hc₀⟩ :=
    exists_critical_in_terminal_model_band_interior data.toTerminalSaddleGeometry
  exact existsUnique_critical_in_cap_of_central_point data i h₀ hc₀

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing
