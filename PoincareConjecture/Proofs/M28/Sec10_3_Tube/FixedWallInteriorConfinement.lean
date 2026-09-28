import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SelectedInteriorWall
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.InteriorEndpointNeckConfinement
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Isotopy.Composition













set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M} {X : Set M}







theorem exists_fixed_wall_interior_confinement
    [MeasurableSpace M] [BorelSpace M] [T3Space M]
    (T : EpsilonTubeCertificate g X)
    (A : OpenCylinderModel T.carrier)
    (U : TopologicalSpace.Opens M)
    (hU : (U : Set M) = A.tail true (1 / 2))
    (hAisotopy : SmoothSphereIsotopicIn T.carrier
      A.middleSphere T.cylinder.middleSphere)
    (R : M → ℝ) (hR : ContinuousOn R T.carrier)
    (hratio : ∀ i ∈ T.chain.shape.active,
      ∀ y ∈ (T.chain.neck i).carrier, ∀ z ∈ (T.chain.neck i).carrier,
        R y ≤ 2 * R z)
    (hdiverge : ∀ C : ℝ, ∃ d : ℝ, 1 / 2 < d ∧ d < 1 ∧
      ∀ x ∈ T.carrier, d < (A.inverse x).2 → C < R x) :
    let V : TopologicalSpace.Opens M := ⟨T.carrier, T.carrier_open⟩
    ∃ i ∈ T.chain.shape.active,
      ∃ (phiMinus : V ≃ₜ (UnitTwoSphere × Ioo (0 : ℝ) 1))
        (aMinus bMinus : ℝ),
        0 < aMinus ∧ aMinus < 1 / 2 ∧
        1 / 2 < bMinus ∧ bMinus < 1 ∧
        (∀ x ∈ V, ambientCylinderSignedHeight phiMinus x = 0 ↔
          x ∈ (T.chain.neck i).central_sphere) ∧
        (∀ x ∈ V, (A.inverse x).2 < aMinus ∨
          bMinus < (A.inverse x).2 →
          ambientCylinderSignedHeight phiMinus x =
            (A.inverse x).2 - 1 / 2) ∧
        (∀ x ∈ V, 0 ≤ ambientCylinderSignedHeight phiMinus x →
          (3 / 4 : ℝ) ≤ (A.inverse x).2) ∧
        (T.chain.neck i).carrier ⊆ A.tail true (3 / 4) ∧
        ∀ {p q : M}, p ∈ V → q ∈ V →
          0 < ambientCylinderSignedHeight phiMinus p →
          0 < ambientCylinderSignedHeight phiMinus q →
          ∃ j ∈ T.chain.shape.active, ∃ c : ℝ,
            max (max bMinus (A.inverse p).2) (A.inverse q).2 < c ∧ c < 1 ∧
            (T.chain.neck j).carrier ⊆ A.tail true c ∧
            ∃ (phiPlus : V ≃ₜ (UnitTwoSphere × Ioo (0 : ℝ) 1))
              (aPlus bPlus : ℝ),
              0 < aPlus ∧ aPlus < 1 / 2 ∧
              1 / 2 < bPlus ∧ bPlus < 1 ∧
              (∀ x ∈ V, ambientCylinderSignedHeight phiPlus x = 0 ↔
                x ∈ (T.chain.neck j).central_sphere) ∧
              (∀ x ∈ V, (A.inverse x).2 < aPlus ∨
                bPlus < (A.inverse x).2 →
                ambientCylinderSignedHeight phiPlus x =
                  (A.inverse x).2 - 1 / 2) ∧
              (∀ x ∈ V, 0 ≤ ambientCylinderSignedHeight phiPlus x →
                c ≤ (A.inverse x).2) ∧
              ∃ (K : Set M) (B : ℝ), IsCompact K ∧ K ⊆ (U : Set M) ∧
                p ∈ K ∧ q ∈ K ∧
                (∀ x ∈ K, (3 / 4 : ℝ) ≤ (A.inverse x).2) ∧
                (3 / 4 : ℝ) < B ∧ B < 1 ∧
                K ⊆ A.compactSlab (3 / 4) B ∧
                ∀ γ : ℝ → M, γ 0 = p → γ 1 = q →
                  ContinuousOn γ (Icc (0 : ℝ) 1) →
                  MapsTo γ (Icc (0 : ℝ) 1) (U : Set M) →
                  ∀ t ∈ Icc (0 : ℝ) 1, γ t ∉ K →
                    ∃ (k : Bool) (s e : ℝ), 0 ≤ s ∧ s ≤ t ∧
                      t ≤ e ∧ e ≤ 1 ∧
                      γ s ∈ (if k then T.chain.neck j
                        else T.chain.neck i).central_sphere ∧
                      γ e ∈ (if k then T.chain.neck j
                        else T.chain.neck i).central_sphere ∧
                      γ t ∉ (if k then T.chain.neck j
                        else T.chain.neck i).region
                          (-((if k then T.chain.neck j
                            else T.chain.neck i).epsilon⁻¹ / 2))
                          ((if k then T.chain.neck j
                            else T.chain.neck i).epsilon⁻¹ / 2) := by
  let V : TopologicalSpace.Opens M := ⟨T.carrier, T.carrier_open⟩
  obtain ⟨i, hi, hNminus⟩ :=
    exists_selected_chain_neck_above_cylinder_level T A R hR hratio hdiverge
      (c := (3 / 4 : ℝ)) (by norm_num) (by norm_num)
  have hIsoMinus : SmoothSphereIsotopicIn (V : Set M)
      (T.chain.neck i).central_sphere A.middleSphere :=
    (T.central_sphere_isotopy i hi).trans hAisotopy.symm
  obtain ⟨phiMinus, aMinus, bMinus, haMinus, haMinusHalf,
      hbMinusHalf, hbMinus, hzeroMinus, htailMinus, hlowerMinus⟩ :=
    exists_fixed_positive_side_above_cylinder_level (V := V)
      (lambda := (3 / 4 : ℝ)) A (T.chain.neck i)
      (by norm_num) (by norm_num) hNminus hIsoMinus
  have hNminusU : (T.chain.neck i).carrier ⊆ (U : Set M) := by
    intro x hx
    have hxTail := (A.mem_tail_iff_m28 true
      (by norm_num : (0 : ℝ) < 3 / 4) (by norm_num : (3 / 4 : ℝ) < 1)).mp
        (hNminus hx)
    rw [hU]
    exact (A.mem_tail_iff_m28 true (by norm_num) (by norm_num)).mpr
      ⟨hxTail.1, (by norm_num : (1 / 2 : ℝ) < 3 / 4).trans hxTail.2⟩
  have hbackSlab : ∀ x ∈ (T.chain.neck i).coordinate_map ''
      (univ ×ˢ Icc (-((T.chain.neck i).epsilon⁻¹ / 2))
        ((T.chain.neck i).epsilon⁻¹ / 2)), (3 / 4 : ℝ) ≤
          (A.inverse x).2 := by
    intro x hx
    have hinv : 0 < (T.chain.neck i).epsilon⁻¹ :=
      inv_pos.mpr (T.chain.neck i).epsilon_pos
    have hcarrier : x ∈ (T.chain.neck i).carrier :=
      (T.chain.neck i).coordinate_slab_subset_carrier_m28
        (by linarith only [hinv]) (by linarith only [hinv]) hx
    have hxTail := (A.mem_tail_iff_m28 true
      (by norm_num : (0 : ℝ) < 3 / 4) (by norm_num : (3 / 4 : ℝ) < 1)).mp
        (hNminus hcarrier)
    exact hxTail.2.le
  refine ⟨i, hi, phiMinus, aMinus, bMinus, haMinus, haMinusHalf,
    hbMinusHalf, hbMinus, hzeroMinus, htailMinus, hlowerMinus,
    hNminus, ?_⟩
  intro p q hp hq hpMinus hqMinus
  have hpHeight : (A.inverse p).2 < 1 := (A.inverse_mem p hp).2.2
  have hqHeight : (A.inverse q).2 < 1 := (A.inverse_mem q hq).2.2
  have hmax : max (max bMinus (A.inverse p).2) (A.inverse q).2 < 1 :=
    max_lt (max_lt hbMinus hpHeight) hqHeight
  obtain ⟨c, hcmax, hc1⟩ := exists_between hmax
  have hcb : bMinus < c :=
    ((le_max_left bMinus (A.inverse p).2).trans
      (le_max_left (max bMinus (A.inverse p).2) (A.inverse q).2)).trans_lt hcmax
  have hcp : (A.inverse p).2 < c :=
    ((le_max_right bMinus (A.inverse p).2).trans
      (le_max_left (max bMinus (A.inverse p).2) (A.inverse q).2)).trans_lt hcmax
  have hcq : (A.inverse q).2 < c :=
    (le_max_right (max bMinus (A.inverse p).2) (A.inverse q).2).trans_lt hcmax
  have hcHalf : 1 / 2 < c := hbMinusHalf.trans hcb
  have hc0 : 0 < c := (by norm_num : (0 : ℝ) < 1 / 2).trans hcHalf
  obtain ⟨j, hj, hNplus⟩ :=
    exists_selected_chain_neck_above_cylinder_level T A R hR hratio hdiverge
      hcHalf hc1
  have hIsoPlus : SmoothSphereIsotopicIn (V : Set M)
      (T.chain.neck j).central_sphere A.middleSphere :=
    (T.central_sphere_isotopy j hj).trans hAisotopy.symm
  obtain ⟨phiPlus, aPlus, bPlus, haPlus, haPlusHalf,
      hbPlusHalf, hbPlus, hzeroPlus, htailPlus, hlowerPlus⟩ :=
    exists_fixed_positive_side_above_cylinder_level (V := V) (lambda := c)
      A (T.chain.neck j) hcHalf hc1 hNplus hIsoPlus
  have hNplusU : (T.chain.neck j).carrier ⊆ (U : Set M) := by
    intro x hx
    have hxTail := (A.mem_tail_iff_m28 true hc0 hc1).mp (hNplus hx)
    rw [hU]
    exact (A.mem_tail_iff_m28 true (by norm_num) (by norm_num)).mpr
      ⟨hxTail.1, hcHalf.trans hxTail.2⟩
  have hpPlus : ambientCylinderSignedHeight phiPlus p < 0 := by
    apply lt_of_not_ge
    intro hnonneg
    exact (not_lt_of_ge (hlowerPlus p hp hnonneg)) hcp
  have hqPlus : ambientCylinderSignedHeight phiPlus q < 0 := by
    apply lt_of_not_ge
    intro hnonneg
    exact (not_lt_of_ge (hlowerPlus q hq hnonneg)) hcq
  have hfrontHigh : ∀ x ∈ V, bPlus < (A.inverse x).2 →
      0 < ambientCylinderSignedHeight phiPlus x := by
    intro x hx hxhigh
    rw [htailPlus x hx (Or.inr hxhigh)]
    exact sub_pos.mpr (hbPlusHalf.trans hxhigh)
  have hfrontSlab : ∀ x ∈ (T.chain.neck j).coordinate_map ''
      (univ ×ˢ Icc (-((T.chain.neck j).epsilon⁻¹ / 2))
        ((T.chain.neck j).epsilon⁻¹ / 2)),
      0 ≤ ambientCylinderSignedHeight phiMinus x := by
    intro x hx
    have hinv : 0 < (T.chain.neck j).epsilon⁻¹ :=
      inv_pos.mpr (T.chain.neck j).epsilon_pos
    have hcarrier : x ∈ (T.chain.neck j).carrier :=
      (T.chain.neck j).coordinate_slab_subset_carrier_m28
        (by linarith only [hinv]) (by linarith only [hinv]) hx
    have hxTail := (A.mem_tail_iff_m28 true hc0 hc1).mp (hNplus hcarrier)
    have hxHigh : bMinus < (A.inverse x).2 := hcb.trans hxTail.2
    rw [htailMinus x hxTail.1 (Or.inr hxHigh)]
    exact sub_nonneg.mpr (hbMinusHalf.trans hxHigh).le
  let N : Bool → EpsilonNeck g := fun k =>
    if k then T.chain.neck j else T.chain.neck i
  have hNU : ∀ k, (N k).carrier ⊆ (U : Set M) := by
    intro k
    cases k with
    | false => exact hNminusU
    | true => exact hNplusU
  obtain ⟨K, B, hK, hKU, hpK, hqK, hheightK, hB3q, hB1,
      hcaptureB, hcross⟩ :=
    exists_interior_endpoint_neck_confinement
      (lambda := (3 / 4 : ℝ)) (bPlus := bPlus)
      g V U A hU N hNU
      (ambientCylinderSignedHeight phiMinus) (ambientCylinderSignedHeight phiPlus)
      (by norm_num) ⟨hbPlusHalf, hbPlus⟩
      (continuousOn_ambientCylinderSignedHeight phiMinus)
      (continuousOn_ambientCylinderSignedHeight phiPlus)
      hzeroMinus hzeroPlus hlowerMinus hbackSlab hfrontSlab hfrontHigh
      hp hq hpMinus hqMinus hpPlus hqPlus
  refine ⟨j, hj, c, hcmax, hc1, hNplus, phiPlus, aPlus, bPlus,
    haPlus, haPlusHalf, hbPlusHalf, hbPlus, hzeroPlus, htailPlus,
    hlowerPlus, K, B, hK, hKU, hpK, hqK, hheightK, hB3q, hB1,
    hcaptureB, ?_⟩
  intro γ hγ0 hγ1 hγ hγU t ht htnot
  simpa only [N] using hcross γ hγ0 hγ1 hγ hγU t ht htnot

end PoincareConjecture.M28
