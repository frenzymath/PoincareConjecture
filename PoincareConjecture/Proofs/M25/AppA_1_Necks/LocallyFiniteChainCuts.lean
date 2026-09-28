import PoincareConjecture.Proofs.M25.AppA_1_Necks.OrderedChainCuts
import PoincareConjecture.Proofs.M25.AppA_1_Necks.ScalarControl
import Mathlib.Topology.LocallyFinite

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.BalancedNeckChain

theorem exists_locallyFinite_retained_slabs :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M} {epsilon : ℝ},
      ∀ (C : BalancedNeckChain g epsilon), epsilon ≤ epsilon0 →
      (∀ i ∈ C.shape.active, (C.neck i).IsSeparating) →
      ∀ a b : ℝ, epsilon⁻¹ / 2 < a → a ≤ b → b < epsilon⁻¹ →
        LocallyFinite (fun i : {i : ℤ // i ∈ C.shape.active} =>
          (C.neck i.1).coordinate_map '' (univ ×ˢ Icc a b)) := by
  obtain ⟨epsilon0, he0, hecap, hcontrol⟩ :=
    EpsilonNeck.exists_normalized_scalar_control_on_carrier.{u} (α := 1 / 2) (by norm_num)
  refine ⟨epsilon0, he0, hecap, ?_⟩
  intro M _ _ _ _ _ _ g epsilon C he hsep a b ha hab hb
  classical
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 3) M
  obtain ⟨i₀, hi₀⟩ := C.active_nonempty
  have hepos : 0 < epsilon := C.epsilon_eq i₀ hi₀ ▸ (C.neck i₀).epsilon_pos
  let L := epsilon⁻¹
  have hL : 0 < L := inv_pos.mpr hepos
  have hroot : 0 < Real.sqrt (1 - epsilon) := Real.sqrt_pos.mpr (by linarith [he.trans hecap])
  have haL : a ∈ Ioo (L / 2) L := ⟨ha, hab.trans_lt hb⟩
  have hbetween {i j k : ℤ} (hi : i ∈ C.shape.active) (hj : j ∈ C.shape.active)
      (hik : i ≤ k) (hkj : k ≤ j) : k ∈ C.shape.active := by
    cases hs : C.shape <;>
      simp only [hs, ChainShape.active, mem_Icc, mem_Ici, mem_Iic, mem_univ] at * <;> omega
  let Kc : ℤ → Set M := fun i => connectedComponent (C.neck i).center
  let S : ℤ → ℝ → Set M := fun i t =>
    range (fun v : UnitTwoSphere => (C.neck i).coordinate_map (v, t))
  let A : ℤ → ℝ → Set M := fun i t => connectedComponentIn (S i t)ᶜ
    ((C.neck i).coordinate_map
      (((C.neck i).coordinate_inverse (C.neck i).center).1, (t - L) / 2))
  obtain ⟨H, _, hH, hK, _, hcuts, horder⟩ := C.exists_ordered_saturated_heights hsep
  change ∀ i ∈ C.shape.active, ∀ j ∈ C.shape.active, Kc i = Kc j at hK
  have hA (i : ℤ) (hi : i ∈ C.shape.active) :
      A i a = Kc i ∩ (H i) ⁻¹' Iio a :=
    (hcuts i hi a ⟨by linarith [haL.1], haL.2⟩).1
  let Z : ℤ → Set M := fun i => (C.neck i).coordinate_map '' (univ ×ˢ Icc a b)
  have hslab {i : ℤ} (hi : i ∈ C.shape.active) {z : M} (hz : z ∈ Z i) :
      z ∈ (C.neck i).carrier ∧ a ≤ H i z ∧ H i z ≤ b := by
    obtain ⟨⟨v, t⟩, hvt, rfl⟩ := hz
    have ht : t ∈ Ioo (-(C.neck i).epsilon⁻¹) (C.neck i).epsilon⁻¹ := by
      rw [C.epsilon_eq i hi]
      constructor <;> linarith [hvt.2.1, hvt.2.2]
    have hc := (C.neck i).coordinate_map_mem (z := (v, t)) ⟨mem_univ _, ht⟩
    refine ⟨hc, ?_⟩
    rw [(hH i hi).2.1 _ hc, (C.neck i).coordinate_inverse_map _ ht]
    exact hvt.2
  have hgap {i j : ℤ} (hi : i ∈ C.shape.active) (hj : j ∈ C.shape.active)
      (hij : i < j) {p q : M} (hp : p ∈ Z i) (hq : q ∈ Z j) :
      i + 1 ∈ C.shape.active ∧ p ∈ (C.neck (i + 1)).carrier ∧
      ENNReal.ofReal ((C.neck (i + 1)).scale * Real.sqrt (1 - epsilon) *
        (a - L / 2)) ≤ g.edist p q := by
    have hn : i + 1 ∈ C.shape.active := hbetween hi hj (by omega) (by omega)
    obtain ⟨hpc, hpa, hpb⟩ := hslab hi hp
    obtain ⟨hqc, hqa, _⟩ := hslab hj hq
    have hpreg : p ∈ (C.neck i).region (L / 2) L := by
      refine ⟨hpc, ?_⟩
      rw [← (hH i hi).2.1 _ hpc]
      exact ⟨ha.trans_le hpa, hpb.trans_lt hb⟩
    have hpn := (C.overlap_contains_quarters i hi hn).1 hpreg
    have hpnH : H (i + 1) p < L / 2 := by
      rw [(hH (i + 1) hn).2.1 _ hpn]
      exact (C.overlap_within_three_quarters i hi hn ⟨hpc, hpn⟩).2.2.2
    have hqnH : a ≤ H (i + 1) q := by
      by_cases heq : i + 1 = j
      · simpa only [heq] using hqa
      · by_contra hnot
        have hqK : q ∈ Kc (i + 1) := by
          have hqKj : q ∈ Kc j := (C.neck j).m25_carrier_subset_connectedComponent hqc
          exact hK j hj (i + 1) hn ▸ hqKj
        have hqA : q ∈ A (i + 1) a := (hA (i + 1) hn).symm ▸ ⟨hqK, lt_of_not_ge hnot⟩
        have hqAj := (horder (i + 1) hn j hj (by omega) a haL a haL).1
          (subset_closure hqA)
        change q ∈ A j a at hqAj
        exact (not_lt_of_ge hqa) (show H j q < a from ((hA j hj) ▸ hqAj).2)
    have hdiff : a - L / 2 ≤ |H (i + 1) p - H (i + 1) q| := by
      rw [abs_sub_comm]
      linarith [le_abs_self (H (i + 1) q - H (i + 1) p)]
    refine ⟨hn, hpn, (ENNReal.ofReal_le_ofReal ?_).trans ((hH (i + 1) hn).2.2.2 p q)⟩
    exact mul_le_mul_of_nonneg_left hdiff
      (mul_nonneg (C.neck (i + 1)).scale_pos.le hroot.le)
  intro x
  let D := (C.neck i₀).connection
  have hscalar (N : EpsilonNeck g) (z : M) :
      N.connection.scalarCurvature z = D.scalarCurvature z := by
    unfold LeviCivitaData.scalarCurvature LeviCivitaData.ricci
    simp_rw [N.connection.horizon_curvatureTensor_eq D z]
  let K := |D.scalarCurvature x| + 1
  have hKpos : 0 < K := by dsimp only [K]; positivity
  let rho := Real.sqrt (1 / (2 * K))
  have hrho : 0 < rho := Real.sqrt_pos.mpr (by positivity)
  have hrhosq : rho ^ 2 = 1 / (2 * K) := Real.sq_sqrt (by positivity)
  have hrhoK : rho ^ 2 * K = 1 / 2 := by
    rw [hrhosq]
    field_simp
  have hscale {i : ℤ} (hi : i ∈ C.shape.active) {z : M}
      (hz : z ∈ (C.neck i).carrier) (hzK : D.scalarCurvature z < K) :
      rho ≤ (C.neck i).scale := by
    have h := hcontrol (C.neck i) (by rw [C.epsilon_eq i hi]; exact he) z hz
    rw [hscalar] at h
    have hlower : (1 : ℝ) / 2 < (C.neck i).scale ^ 2 * D.scalarCurvature z := by
      linarith [(abs_lt.mp h).1]
    have hupper := mul_lt_mul_of_pos_left hzK (sq_pos_of_pos (C.neck i).scale_pos)
    by_contra hn
    have hsq : (C.neck i).scale ^ 2 < rho ^ 2 :=
      (sq_lt_sq₀ (C.neck i).scale_pos.le hrho.le).mpr (lt_of_not_ge hn)
    have hprod := mul_lt_mul_of_pos_right hsq hKpos
    rw [hrhoK] at hprod
    linarith
  let d := rho * Real.sqrt (1 - epsilon) * (a - L / 2)
  have hd : 0 < d := mul_pos (mul_pos hrho hroot) (sub_pos.mpr ha)
  let V := {z | D.scalarCurvature z < K} ∩ {z | g.edist z x < ENNReal.ofReal (d / 3)}
  have hV : IsOpen V :=
    (isOpen_lt D.continuous_scalarCurvature continuous_const).inter
      (isOpen_lt (continuous_id.edist continuous_const) continuous_const)
  have hxV : x ∈ V := by
    refine ⟨?_, ?_⟩
    · change D.scalarCurvature x < |D.scalarCurvature x| + 1
      linarith [le_abs_self (D.scalarCurvature x)]
    · change edist x x < ENNReal.ofReal (d / 3)
      simpa only [edist_self] using ENNReal.ofReal_pos.mpr (div_pos hd (by norm_num))
  have hnotboth {i j : ℤ} (hi : i ∈ C.shape.active) (hj : j ∈ C.shape.active)
      (hij : i < j) {p q : M} (hp : p ∈ Z i) (hpV : p ∈ V)
      (hq : q ∈ Z j) (hqV : q ∈ V) : False := by
    obtain ⟨hn, hpn, hdist⟩ := hgap hi hj hij hp hq
    have hscaleN := hscale hn hpn hpV.1
    have hdlower : ENNReal.ofReal d ≤ g.edist p q := by
      apply (ENNReal.ofReal_le_ofReal ?_).trans hdist
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hscaleN hroot.le) (sub_nonneg.mpr ha.le)
    have hdupper : g.edist p q < ENNReal.ofReal d := by
      calc
        g.edist p q ≤ g.edist p x + g.edist x q := edist_triangle p x q
        _ < ENNReal.ofReal (d / 3) + ENNReal.ofReal (d / 3) :=
          ENNReal.add_lt_add hpV.2 (by
            change edist x q < _
            rw [edist_comm]
            exact hqV.2)
        _ < ENNReal.ofReal d := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          exact (ENNReal.ofReal_lt_ofReal_iff hd).mpr (by linarith)
    exact not_lt_of_ge hdlower hdupper
  refine ⟨V, hV.mem_nhds hxV, Set.Subsingleton.finite ?_⟩
  intro i hi j hj
  obtain ⟨p, hp, hpV⟩ := hi
  obtain ⟨q, hq, hqV⟩ := hj
  apply Subtype.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact hnotboth i.2 j.2 hij hp hpV hq hqV
  · exact hnotboth j.2 i.2 hji hq hqV hp hpV

end PoincareConjecture.BalancedNeckChain
