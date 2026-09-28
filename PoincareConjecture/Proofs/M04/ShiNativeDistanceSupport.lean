import PoincareConjecture.Proofs.M04.ShiPiecewiseEnergy
import PoincareConjecture.Proofs.M04.ShiEnergyPaths
import PoincareConjecture.Proofs.M04.ShiEnergyDistanceSupport
import PoincareConjecture.Proofs.M04.ShiEnergyJetBounds
import PoincareConjecture.Proofs.M04.ShiNormalCoordinates
import PoincareConjecture.Proofs.M04.ShiPathTuples
import PoincareConjecture.Proofs.M04.ShiUniformJoinedAtlas

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff Bundle ENNReal BigOperators

universe u

namespace PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "End" => V →L[ℝ] V

private theorem shiNative_clm_deriv
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (L : X →L[ℝ] Y) {f : ℝ → X} {f' : X} {s : Set ℝ} {t : ℝ}
    (hf : HasDerivWithinAt f f' s t) :
    HasDerivWithinAt (fun a => L (f a)) (L f') s t :=
  HasFDerivAt.comp_hasDerivWithinAt (𝕜 := ℝ) (F := X) (E := Y)
    (l := L) (f := f) t L.hasFDerivAt hf

private theorem shiNative_neg_deriv
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f : ℝ → X} {f' : X} {s : Set ℝ} {t : ℝ}
    (hf : HasDerivWithinAt f f' s t) :
    HasDerivWithinAt (fun a => -f a) (-f') s t :=
  hf.neg

set_option maxHeartbeats 1200000 in

set_option synthInstance.maxHeartbeats 100000 in
set_option backward.isDefEq.respectTransparency false in
private theorem shiNative_bilinear_deriv
    {G : ℝ → V →L[ℝ] V →L[ℝ] V} {A : ℝ → V →L[ℝ] V}
    {H : V →L[ℝ] V →L[ℝ] V} {J : V →L[ℝ] V} {s : Set ℝ} {t : ℝ}
    (hG : HasDerivWithinAt G H s t) (hA : HasDerivWithinAt A J s t) :
    HasDerivWithinAt (fun a => -(G a).bilinearComp (A a) (A a))
      (-H.bilinearComp (A t) (A t) - (G t).bilinearComp J (A t) -
        (G t).bilinearComp (A t) J) s t := by
  let L :=
    (ContinuousLinearMap.flipₗᵢ ℝ V V V).toLinearIsometry.toContinuousLinearMap
  have hflip {f : ℝ → V →L[ℝ] V →L[ℝ] V} {f' : V →L[ℝ] V →L[ℝ] V}
      (hf : HasDerivWithinAt f f' s t) :
      HasDerivWithinAt (fun a => (f a).flip) f'.flip s t := by
    have hh := shiNative_clm_deriv
      (X := V →L[ℝ] V →L[ℝ] V) (Y := V →L[ℝ] V →L[ℝ] V) L hf
    simpa +instances only [L, ContinuousLinearMap.coe_flipₗᵢ] using! hh
  have h := hflip ((hflip (hG.clm_comp hA)).clm_comp hA)
  have hneg : HasDerivWithinAt
      (fun a => -(((G a).comp (A a)).flip.comp (A a)).flip)
      (-(((H.comp (A t) + (G t).comp J).flip.comp (A t) +
        ((G t).comp (A t)).flip.comp J).flip)) s t := by
    exact shiNative_neg_deriv (X := V →L[ℝ] V →L[ℝ] V) h
  have hfun : (fun a => -(((G a).comp (A a)).flip.comp (A a)).flip) =
      (fun a => -(G a).bilinearComp (A a) (A a)) := rfl
  have heq : -(((H.comp (A t) + (G t).comp J).flip.comp (A t) +
      ((G t).comp (A t)).flip.comp J).flip) =
      -H.bilinearComp (A t) (A t) - (G t).bilinearComp J (A t) -
        (G t).bilinearComp (A t) J := by
    ext v w : 2
    simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.bilinearComp_apply, add_apply, sub_apply, neg_apply]
    abel
  rw [hfun, heq] at hneg
  exact hneg

theorem shi_partition_integral_eq
    (N : ℕ) (τ : ℕ → ℝ) (f : ℝ → ℝ)
    (hN : 0 < N)
    (hstep : ∀ i, i < N → τ i < τ (i + 1))
    (hzero : τ 0 = 0) (hone : τ N = 1)
    (hτ : ∀ i, i ≤ N → 0 ≤ τ i ∧ τ i ≤ 1)
    (hf : ContinuousOn f (Icc (0 : ℝ) 1)) :
    (∑ i ∈ Finset.range N, ∫ t in τ i..τ (i + 1), f t) =
      ∫ t in (0 : ℝ)..1, f t := by
  have hinterval (i : ℕ) (hi : i < N) :
      IntervalIntegrable f volume (τ i) (τ (i + 1)) := by
    apply ContinuousOn.intervalIntegrable_of_Icc (hstep i hi).le
    apply hf.mono
    intro t ht
    have hbounds := hτ i (Nat.le_of_lt hi)
    have hbounds' := hτ (i + 1) (Nat.succ_le_of_lt hi)
    exact ⟨hbounds.1.trans ht.1, ht.2.trans hbounds'.2⟩
  rw [intervalIntegral.sum_integral_adjacent_intervals hinterval, hzero, hone]

theorem shi_segment_energy_partition
    (g : RiemannianMetric n M) (N : ℕ) (τ : ℕ → ℝ)
    (γ : ℕ → ℝ → M) (γ₀ : ℝ → M)
    (hN : 0 < N)
    (hstep : ∀ i, i < N → τ i < τ (i + 1))
    (hzero : τ 0 = 0) (hone : τ N = 1)
    (hτ : ∀ i, i ≤ N → 0 ≤ τ i ∧ τ i ≤ 1)
    (hγ : ∀ i, i < N →
      ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 (γ i) (Icc (τ i) (τ (i + 1))))
    (hpoint : ∀ i, i < N → ∀ t, t ∈ Icc (τ i) (τ (i + 1)) →
      (segmentPathSpeed g (γ i) (τ i) (τ (i + 1)) t) ^ 2 =
        (pathSpeed g γ₀ t) ^ 2)
    (hγ₀ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 γ₀) :
    (∑ i ∈ Finset.range N,
      segmentPathEnergy g (γ i) (τ i) (τ (i + 1))) =
      pathEnergy g γ₀ := by
  have hspeed : ContinuousOn (pathSpeed g γ₀) (Icc (0 : ℝ) 1) :=
    (continuous_pathSpeed g hγ₀).continuousOn
  have hseg (i : ℕ) (hi : i < N) :
      segmentPathEnergy g (γ i) (τ i) (τ (i + 1)) =
        ∫ t in τ i..τ (i + 1), (pathSpeed g γ₀ t) ^ 2 := by
    rw [segmentPathEnergy_eq_integral_segmentPathSpeed_sq]
    apply intervalIntegral.integral_congr
    intro t ht
    exact hpoint i hi t (by simpa only [uIcc_of_le (hstep i hi).le] using ht)
  calc
    (∑ i ∈ Finset.range N,
        segmentPathEnergy g (γ i) (τ i) (τ (i + 1))) =
        ∑ i ∈ Finset.range N,
          ∫ t in τ i..τ (i + 1), (pathSpeed g γ₀ t) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hseg i (Finset.mem_range.mp hi)
    _ = ∫ t in (0 : ℝ)..1, (pathSpeed g γ₀ t) ^ 2 := by
      apply shi_partition_integral_eq N τ (fun t => (pathSpeed g γ₀ t) ^ 2)
        hN hstep hzero hone hτ
      exact hspeed.pow 2
    _ = pathEnergy g γ₀ := (pathEnergy_eq_integral_pathSpeed_sq g γ₀).symm

theorem shi_mesh_actual_density_zero_energy
    (g : RiemannianMetric n M) (N : ℕ) (τ : ℕ → ℝ)
    (γ : ℝ → M) (e : ℕ → ℝ → ℝ)
    (hN : 0 < N)
    (hstep : ∀ i, i < N → τ i < τ (i + 1))
    (hzero : τ 0 = 0) (hone : τ N = 1)
    (hτ : ∀ i, i ≤ N → 0 ≤ τ i ∧ τ i ≤ 1)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 γ)
    (he : ∀ i, i < N → ∀ t, t ∈ Icc (τ i) (τ (i + 1)) →
      e i t = (pathSpeed g γ t) ^ 2) :
    (∑ i ∈ Finset.range N, ∫ t in τ i..τ (i + 1), e i t) =
      pathEnergy g γ := by
  have hspeed : ContinuousOn (pathSpeed g γ) (Icc (0 : ℝ) 1) :=
    (continuous_pathSpeed g hγ).continuousOn
  calc
    (∑ i ∈ Finset.range N, ∫ t in τ i..τ (i + 1), e i t) =
        ∑ i ∈ Finset.range N, ∫ t in τ i..τ (i + 1),
          (pathSpeed g γ t) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      apply intervalIntegral.integral_congr
      intro t ht
      exact he i (Finset.mem_range.mp hi) t
        (by simpa only [uIcc_of_le (hstep i (Finset.mem_range.mp hi)).le] using ht)
    _ = ∫ t in (0 : ℝ)..1, (pathSpeed g γ t) ^ 2 := by
      apply shi_partition_integral_eq N τ (fun t => (pathSpeed g γ t) ^ 2)
        hN hstep hzero hone hτ
      exact hspeed.pow 2
    _ = pathEnergy g γ := (pathEnergy_eq_integral_pathSpeed_sq g γ).symm

set_option backward.isDefEq.respectTransparency false in
theorem shi_segmentPathEnergy_eq_chartMetric_integral
    (g : RiemannianMetric n M) {c : OpenPartialHomeomorph M V}
    (hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, V) ∞ c c.source)
    (hi : ContMDiffOn 𝓘(ℝ, V) (𝓡 n) ∞ c.symm c.target)
    {a b : ℝ} (hab : a < b) (F : ℝ → V → V) (z : V)
    (hF : ContDiffOn ℝ 1 (fun t => F t z) (Icc a b))
    (hFtarget : ∀ t, t ∈ Icc a b → F t z ∈ c.target) :
    segmentPathEnergy g (fun t => c.symm (F t z)) a b =
      ∫ t in a..b, shiChartMetric g c (F t z)
        (derivWithin (fun s => F s z) (Icc a b) t)
        (derivWithin (fun s => F s z) (Icc a b) t) := by
  unfold segmentPathEnergy
  apply intervalIntegral.integral_congr
  intro t ht'
  have ht : t ∈ Icc a b := by simpa only [uIcc_of_le hab.le] using ht'
  have hFD : DifferentiableWithinAt ℝ (fun s => F s z) (Icc a b) t :=
    hF.differentiableOn (by norm_num) t ht
  have hFM : MDifferentiableWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, V)
      (fun s => F s z) (Icc a b) t := hFD.mdifferentiableWithinAt
  have hcg : MDifferentiableAt 𝓘(ℝ, V) (𝓡 n) c.symm (F t z) :=
    (hi.contMDiffAt (c.open_target.mem_nhds (hFtarget t ht))).mdifferentiableAt (by simp)
  have hcomp := mfderiv_comp_mfderivWithin t
    (f := fun s => F s z) (g := c.symm) (s := Icc a b)
    hcg hFM ((uniqueDiffOn_Icc hab).uniqueMDiffOn t ht)
  have hvel :
      mfderivWithin 𝓘(ℝ, ℝ) (𝓡 n)
          (c.symm ∘ (fun s => F s z)) (Icc a b) t 1 =
        mfderiv 𝓘(ℝ, V) (𝓡 n) c.symm (F t z)
          (derivWithin (fun s => F s z) (Icc a b) t) := by
    have hcomp' := congrArg (fun L => L (1 : ℝ)) hcomp
    change _ = mfderiv 𝓘(ℝ, V) (𝓡 n) c.symm (F t z)
      (mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, V) (fun s => F s z) (Icc a b) t 1) at hcomp'
    simpa +instances only [mfderivWithin_eq_fderivWithin, derivWithin, Function.comp_def]
      using! hcomp'
  change g.inner (c.symm (F t z))
      (mfderivWithin 𝓘(ℝ, ℝ) (𝓡 n)
        (c.symm ∘ (fun s => F s z)) (Icc a b) t 1)
      (mfderivWithin 𝓘(ℝ, ℝ) (𝓡 n)
        (c.symm ∘ (fun s => F s z)) (Icc a b) t 1) = _
  rw [hvel]
  rfl

theorem shiActualJoinedDensity_integral_eq_segmentPathEnergy
    (D : LeviCivitaData g) {c : OpenPartialHomeomorph M V}
    (hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, V) ∞ c c.source)
    (hi : ContMDiffOn 𝓘(ℝ, V) (𝓡 n) ∞ c.symm c.target)
    {a b : ℝ} (hab : a < b) (x : ℝ → V) (P : ℝ → End)
    (left right : V → V) (z : V)
    (hF : ContDiffOn ℝ 1
      (fun t => joinedCoordinateVariation a b x
        (fun s => s • P s)
        (fun s => -(shiChartChristoffel D c (x s)).bilinearComp
          (s • P s) (s • P s)) left right t z) (Icc a b))
    (hFtarget : ∀ t, t ∈ Icc a b →
      joinedCoordinateVariation a b x
        (fun s => s • P s)
        (fun s => -(shiChartChristoffel D c (x s)).bilinearComp
          (s • P s) (s • P s)) left right t z ∈ c.target) :
    ∫ t in a..b, shiActualJoinedDensity D c a b x P left right t z =
      segmentPathEnergy g
        (fun t => c.symm (joinedCoordinateVariation a b x
          (fun s => s • P s)
          (fun s => -(shiChartChristoffel D c (x s)).bilinearComp
            (s • P s) (s • P s)) left right t z)) a b := by
  let F : ℝ → V → V := joinedCoordinateVariation a b x
    (fun s => s • P s)
    (fun s => -(shiChartChristoffel D c (x s)).bilinearComp
      (s • P s) (s • P s)) left right
  have h := shi_segmentPathEnergy_eq_chartMetric_integral g hc hi hab F z hF hFtarget
  simpa only [shiActualJoinedDensity, F] using h.symm

theorem shiPath_density_eq_actual_of_position_velocity
    {m N : ℕ} (D : LeviCivitaData g)
    (c : Fin m → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (cstar : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (label : Fin N → Fin m) (γ : ℝ → M)
    (P : Fin N → ℝ →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (j : Fin N)
    (t : ℝ) (z : EuclideanSpace ℝ (Fin n))
    (hpos :
      shiPathJoinedVariation D c cstar label γ P j t z =
        shiJoinedPosition D (c (label j))
          (shiPathVertexChart c cstar label j.castSucc)
          (shiPathVertexChart c cstar label j.succ)
          (shiPathTime N j.val) (shiPathTime N (j.val + 1))
          (shiPathTuple c cstar label γ P j t) z)
    (hvel :
      derivWithin
          (fun s => shiPathJoinedVariation D c cstar label γ P j s z)
          (Icc (shiPathTime N j.val) (shiPathTime N (j.val + 1))) t =
        shiJoinedVelocity D (c (label j))
          (shiPathVertexChart c cstar label j.castSucc)
          (shiPathVertexChart c cstar label j.succ)
          (shiPathTime N j.val) (shiPathTime N (j.val + 1))
          (shiPathTuple c cstar label γ P j t) z) :
      shiJoinedDensity g D (c (label j))
          (shiPathVertexChart c cstar label j.castSucc)
          (shiPathVertexChart c cstar label j.succ)
          (shiPathTime N j.val) (shiPathTime N (j.val + 1))
          (shiPathTuple c cstar label γ P j t) z =
        shiActualJoinedDensity D (c (label j))
          (shiPathTime N j.val) (shiPathTime N (j.val + 1))
          ((c (label j)) ∘ γ) (P j)
          (shiPathEndpoint D c cstar label γ P j j.castSucc)
          (shiPathEndpoint D c cstar label γ P j j.succ) t z := by
  simp only [shiJoinedDensity, shiActualJoinedDensity]
  change shiChartMetric g (c (label j))
      (shiJoinedPosition D (c (label j))
        (shiPathVertexChart c cstar label j.castSucc)
        (shiPathVertexChart c cstar label j.succ)
        (shiPathTime N j.val) (shiPathTime N (j.val + 1))
        (shiPathTuple c cstar label γ P j t) z)
      (shiJoinedVelocity D (c (label j))
        (shiPathVertexChart c cstar label j.castSucc)
        (shiPathVertexChart c cstar label j.succ)
        (shiPathTime N j.val) (shiPathTime N (j.val + 1))
        (shiPathTuple c cstar label γ P j t) z)
      (shiJoinedVelocity D (c (label j))
        (shiPathVertexChart c cstar label j.castSucc)
        (shiPathVertexChart c cstar label j.succ)
        (shiPathTime N j.val) (shiPathTime N (j.val + 1))
        (shiPathTuple c cstar label γ P j t) z) =
    shiChartMetric g (c (label j))
      (shiPathJoinedVariation D c cstar label γ P j t z)
      (derivWithin (fun s => shiPathJoinedVariation D c cstar label γ P j s z)
        (Icc (shiPathTime N j.val) (shiPathTime N (j.val + 1))) t)
      (derivWithin (fun s => shiPathJoinedVariation D c cstar label γ P j s z)
        (Icc (shiPathTime N j.val) (shiPathTime N (j.val + 1))) t)
  rw [hpos, hvel]

set_option maxHeartbeats 1800000 in

set_option synthInstance.maxHeartbeats 100000 in
set_option backward.isDefEq.respectTransparency false in
theorem shiPathTuple_density_eq_actual
    [T2Space M] {m N : ℕ} (D : LeviCivitaData g)
    (hN : 0 < N) (c : Fin m → OpenPartialHomeomorph M V)
    (cstar : OpenPartialHomeomorph M V) (label : Fin N → Fin m)
    (γ : ℝ → M) (P : Fin N → ℝ → End)
    (hc : ∀ i, ContMDiffOn (𝓡 n) 𝓘(ℝ, V) ∞ (c i) (c i).source)
    (hi : ∀ i, ContMDiffOn 𝓘(ℝ, V) (𝓡 n) ∞ (c i).symm (c i).target)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 γ)
    (hinside : ∀ j : Fin N, MapsTo γ
      (Icc (shiPathTime N j.val) (shiPathTime N (j.val + 1))) (c (label j)).source)
    (hPd : ∀ j t, t ∈ Icc (shiPathTime N j.val) (shiPathTime N (j.val + 1)) →
      HasDerivWithinAt (P j)
        (-((shiChartChristoffel D (c (label j)) (c (label j) (γ t))
          (deriv ((c (label j)) ∘ γ) t)).comp (P j t)))
        (Icc (shiPathTime N j.val) (shiPathTime N (j.val + 1))) t)
    (hq : γ 1 ∈ cstar.source)
    (hPL : ∀ j : Fin N, P j (shiPathTime N j.val) =
      (fderiv ℝ ((c (label j)) ∘
        (shiPathVertexChart c cstar label j.castSucc).symm)
        (shiPathVertexCoordinate c cstar label γ j.castSucc)).comp
        (shiPathVertexFrame P j.castSucc))
    (hPR : ∀ j : Fin N, P j (shiPathTime N (j.val + 1)) =
      (fderiv ℝ ((c (label j)) ∘
        (shiPathVertexChart c cstar label j.succ).symm)
        (shiPathVertexCoordinate c cstar label γ j.succ)).comp
        (shiPathVertexFrame P j.succ))
    (j : Fin N) (t : ℝ)
    (ht : t ∈ Icc (shiPathTime N j.val) (shiPathTime N (j.val + 1)))
    (z : V) :
    shiJoinedDensity g D (c (label j))
        (shiPathVertexChart c cstar label j.castSucc)
        (shiPathVertexChart c cstar label j.succ)
        (shiPathTime N j.val) (shiPathTime N (j.val + 1))
        (shiPathTuple c cstar label γ P j t) z =
      shiActualJoinedDensity D (c (label j))
        (shiPathTime N j.val) (shiPathTime N (j.val + 1))
        ((c (label j)) ∘ γ) (P j)
        (shiPathEndpoint D c cstar label γ P j j.castSucc)
        (shiPathEndpoint D c cstar label γ P j j.succ) t z := by
  let a : ℝ := shiPathTime N j.val
  let b : ℝ := shiPathTime N (j.val + 1)
  let x : ℝ → V := (c (label j)) ∘ γ
  let Γ : V → V →L[ℝ] V →L[ℝ] V := shiChartChristoffel D (c (label j))
  let A : ℝ → End := fun s => s • P j s
  let T : V := deriv (x) t
  let J : End := P j t - (Γ (x t) T).comp (A t)
  let H := fderiv ℝ Γ (x t) T
  let B : ℝ → V →L[ℝ] V →L[ℝ] V := fun s =>
    -(Γ (x s)).bilinearComp (A s) (A s)
  let B1 := -H.bilinearComp (A t) (A t) -
    (Γ (x t)).bilinearComp J (A t) -
    (Γ (x t)).bilinearComp (A t) J
  have hab : a < b := by
    exact shiPathTime_step hN j.val
  have hcoord := shiPath_coordinate_regular (hc (label j)) hγ hab
    (hinside j)
  have hxd0 : HasDerivWithinAt x
      (derivWithin x (Icc a b) t) (Icc a b) t := by
    exact ((hcoord.1.differentiableOn (by norm_num) t ht).hasDerivWithinAt)
  have hxd : HasDerivWithinAt x T (Icc a b) t := by
    apply hxd0.congr_deriv
    simpa only [x, Function.comp_apply] using hcoord.2.2 t ht
  have hA : HasDerivWithinAt A J (Icc a b) t := by
    have h := (hasDerivWithinAt_id t (Icc a b)).smul (hPd j t ht)
    apply h.congr_deriv
    ext v : 1
    simp only [A, J, Γ, T, x, id_eq, one_smul, add_apply, sub_apply, neg_apply,
      smul_apply, ContinuousLinearMap.comp_apply, map_smul, smul_neg,
      Function.comp_apply]
    abel_nf
  have hxt : x t ∈ (c (label j)).target :=
    (c (label j)).map_source (hinside j ht)
  have hΓ : DifferentiableAt ℝ Γ (x t) :=
    ((shiChartChristoffel_smooth D (hc (label j)) (hi (label j))).contDiffAt
      ((c (label j)).open_target.mem_nhds hxt)).differentiableAt (by simp)
  have hG : HasDerivWithinAt (fun s => Γ (x s)) H (Icc a b) t :=
    HasFDerivAt.comp_hasDerivWithinAt (𝕜 := ℝ)
      (F := V) (E := V →L[ℝ] V →L[ℝ] V) (l := Γ) (f := x) t
      hΓ.hasFDerivAt hxd
  have hB : HasDerivWithinAt B B1 (Icc a b) t :=
    shiNative_bilinear_deriv hG hA
  have hInv (k : Fin (N + 1)) : (shiPathVertexChart c cstar label k).symm
      (shiPathVertexCoordinate c cstar label γ k) = γ (shiPathTime N k.val) :=
    (shiPathVertexChart c cstar label k).left_inv
      (shiPath_vertex_source hN c cstar label γ hinside hq k)
  have hraw (s : ℝ) : quadraticPathJet (x s) (A s) (B s) z =
      shiRawCoordinateVariation D (c (label j)) s (c (label j) (γ s)) (P j s) z := by
    simp only [quadraticPathJet, shiRawCoordinateVariation, x, A, B, Γ,
      Function.comp_apply, neg_apply, ContinuousLinearMap.bilinearComp_apply,
      smul_apply, smul_neg, sub_eq_add_neg]
  have hleft : shiJoinedDiscrepancy D (c (label j))
      (shiPathVertexChart c cstar label j.castSucc) a
      (shiPathVertexCoordinate c cstar label γ j.castSucc)
      (shiPathVertexFrame P j.castSucc) z =
        shiPathEndpoint D c cstar label γ P j j.castSucc z -
          quadraticPathJet (x a) (A a) (B a) z := by
    rw [hraw a]
    simp only [shiJoinedDiscrepancy, shiJoinedRawEndpoint, shiJoinedTransition,
      shiPathEndpoint, shiPathVertexMap, Function.comp_apply, hInv, Fin.val_castSucc,
      ← hPL j, a]
  have hright : shiJoinedDiscrepancy D (c (label j))
      (shiPathVertexChart c cstar label j.succ) b
      (shiPathVertexCoordinate c cstar label γ j.succ)
      (shiPathVertexFrame P j.succ) z =
        shiPathEndpoint D c cstar label γ P j j.succ z -
          quadraticPathJet (x b) (A b) (B b) z := by
    rw [hraw b]
    simp only [shiJoinedDiscrepancy, shiJoinedRawEndpoint, shiJoinedTransition,
      shiPathEndpoint, shiPathVertexMap, Function.comp_apply, hInv, Fin.val_succ,
      ← hPR j, b]
  have hvel0 := (hasDerivWithinAt_joinedCoordinateVariation a b t z x A B
    (shiPathEndpoint D c cstar label γ P j j.castSucc)
    (shiPathEndpoint D c cstar label γ P j j.succ)
    T J B1 hxd hA hB).derivWithin
      ((uniqueDiffOn_Icc hab).uniqueDiffWithinAt ht)
  have hvel : derivWithin
      (fun s => shiPathJoinedVariation D c cstar label γ P j s z)
      (Icc (shiPathTime N j.val) (shiPathTime N (j.val + 1))) t =
      shiJoinedVelocity D (c (label j))
        (shiPathVertexChart c cstar label j.castSucc)
        (shiPathVertexChart c cstar label j.succ) a b
        (shiPathTuple c cstar label γ P j t) z := by
    have hformula :
        shiJoinedVelocity D (c (label j))
          (shiPathVertexChart c cstar label j.castSucc)
          (shiPathVertexChart c cstar label j.succ) a b
          (shiPathTuple c cstar label γ P j t) z =
        T + J z + (1 / 2 : ℝ) • B1 z z + (b - a)⁻¹ •
          ((shiPathEndpoint D c cstar label γ P j j.succ z -
            quadraticPathJet (x b) (A b) (B b) z) -
           (shiPathEndpoint D c cstar label γ P j j.castSucc z -
            quadraticPathJet (x a) (A a) (B a) z)) := by
      simp only [shiJoinedVelocity, shiPathTuple, joinedYL, joinedQL, joinedYR,
        joinedQR, hleft, hright, joinedTime, joinedX, joinedT, joinedP,
        shiJoinedA, shiJoinedJ, A, B1, H, J, T, x, Γ, Function.comp_apply,
        ContinuousLinearMap.bilinearComp_apply, ContinuousLinearMap.comp_apply,
        sub_apply, neg_apply, smul_apply, smul_add, smul_sub, smul_neg]
      abel
    simpa only [shiPathJoinedVariation, a, b, x, A, B, Γ, Function.comp_apply]
      using Eq.trans hvel0 hformula.symm
  have hpos := shiPathJoinedVariation_eq_position D hN c cstar label γ P
    hinside hq j (hPL j) (hPR j) t z
  exact shiPath_density_eq_actual_of_position_velocity D c cstar label γ P j t z
    hpos hvel

theorem shiActualJoinedDensity_zero_eq_chart_metric_deriv
    (D : LeviCivitaData g) {c : OpenPartialHomeomorph M V}
    {a b : ℝ} (hab : a < b) (x : ℝ → V)
    (P : ℝ → End) (left right : V → V)
    (hl0 : left 0 = x a) (hr0 : right 0 = x b)
    (t : ℝ) (ht : t ∈ Icc a b)
    (hderiv : derivWithin x (Icc a b) t = deriv x t) :
    shiActualJoinedDensity D c a b x P left right t 0 =
      shiChartMetric g c (x t) (deriv x t) (deriv x t) := by
  let A : ℝ → End := fun s => s • P s
  let B : ℝ → V →L[ℝ] V →L[ℝ] V := fun s =>
    -(shiChartChristoffel D c (x s)).bilinearComp (A s) (A s)
  let F := joinedCoordinateVariation a b x A B left right
  have hF (s : ℝ) : F s 0 = x s := by
    simp only [F, joinedCoordinateVariation, quadraticPathJet, map_zero,
      smul_zero, add_zero, hl0, hr0, sub_self]
  have hW : derivWithin (fun s => F s 0) (Icc a b) t = deriv x t := by
    rw [show (fun s => F s 0) = x by funext s; exact hF s, hderiv]
  change shiChartMetric g c (F t 0)
    (derivWithin (fun s => F s 0) (Icc a b) t)
    (derivWithin (fun s => F s 0) (Icc a b) t) = _
  rw [hF t, hW]

theorem shiActualJoinedDensity_zero_eq_pathSpeed_sq
    (D : LeviCivitaData g) {c : OpenPartialHomeomorph M V}
    {a b : ℝ} (hab : a < b) (γ : ℝ → M)
    (P : ℝ → End) (left right : V → V)
    (hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, V) ∞ c c.source)
    (hi : ContMDiffOn 𝓘(ℝ, V) (𝓡 n) ∞ c.symm c.target)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 γ)
    (hinside : MapsTo γ (Icc a b) c.source)
    (hl0 : left 0 = (c ∘ γ) a) (hr0 : right 0 = (c ∘ γ) b)
    (t : ℝ) (ht : t ∈ Icc a b) :
    shiActualJoinedDensity D c a b (c ∘ γ) P left right t 0 =
      (pathSpeed g γ t) ^ 2 := by
  have hcoord := shiPath_coordinate_regular hc hγ hab hinside
  have hzero := shiActualJoinedDensity_zero_eq_chart_metric_deriv (c := c) D hab
    (c ∘ γ) P left right hl0 hr0 t ht (hcoord.2.2 t ht)
  have hmetric := shiChart_coordinate_velocity_metric (g := g) hc hi hγ
    (hinside ht)
  have hnonneg : 0 ≤ shiChartMetric g c ((c ∘ γ) t)
      (deriv (c ∘ γ) t) (deriv (c ∘ γ) t) := by
    by_cases hv : deriv (c ∘ γ) t = 0
    · simp [hv]
    · exact (shiChartMetric_pos g hc hi (c.map_source (hinside ht)) hv).le
  calc
    shiActualJoinedDensity D c a b (c ∘ γ) P left right t 0 =
        shiChartMetric g c ((c ∘ γ) t)
          (deriv (c ∘ γ) t) (deriv (c ∘ γ) t) := hzero
    _ = (Real.sqrt (shiChartMetric g c ((c ∘ γ) t)
          (deriv (c ∘ γ) t) (deriv (c ∘ γ) t))) ^ 2 :=
      (Real.sq_sqrt hnonneg).symm
    _ = (pathSpeed g γ t) ^ 2 := by
      simpa only [Function.comp_apply] using congrArg (fun r : ℝ => r ^ 2) hmetric.2

theorem shi_pullback_energy_support
    [T2Space M] (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (p q : M) (cstar : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (J : EuclideanSpace ℝ (Fin n) ≃L[ℝ] TangentSpace (𝓡 n) q)
    (σ : Fin n ≃ Fin (Module.finrank ℝ (TangentSpace (𝓡 n) q)))
    (hq : q ∈ cstar.source) (h0 : cstar q = 0)
    (hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
      cstar cstar.source)
    (hi : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) ∞
      cstar.symm cstar.target)
    (hJ : ∀ i, J (EuclideanSpace.basisFun (Fin n) ℝ i) =
      g.orthonormalBasis q (σ i))
    (hd : mvfderiv (𝓡 n) cstar q =
      (J.symm : TangentSpace (𝓡 n) q →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (hH : ∀ i a b, D.hessian (fun y => cstar y i) q a b = 0)
    (r : ℝ) (hr : 0 < r) (P : EuclideanSpace ℝ (Fin n) → ℝ)
    (hP : ContDiff ℝ ∞ P) (hP0 : P 0 = (g.edist p q).toReal)
    (hfinite : ∀ z, ‖z‖ < r →
      g.edist p (cstar.symm z) ≠ (⊤ : ℝ≥0∞))
    (hmajor : ∀ z, ‖z‖ < r →
      (g.edist p (cstar.symm z)).toReal ≤ P z)
    (hgrad : ‖fderiv ℝ P 0‖ ≤ 1)
    (K ε : ℝ)
    (htrace : (∑ i : Fin n, fderiv ℝ (fderiv ℝ P) 0
      (EuclideanSpace.basisFun (Fin n) ℝ i)
      (EuclideanSpace.basisFun (Fin n) ℝ i)) ≤
      (n : ℝ) / (g.edist p q).toReal +
        (n : ℝ) * K * (g.edist p q).toReal + ε) :
    ∃ (U : Set M) (u : M → ℝ),
      IsOpen U ∧ q ∈ U ∧
      ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ u U ∧
      u q = (g.edist p q).toReal ∧
      (∀ y ∈ U, g.edist p y ≤ ENNReal.ofReal (u y)) ∧
      scalarGradientSq g u q ≤ 1 ∧
      D.laplacian u q ≤
        (n : ℝ) / (g.edist p q).toReal +
          (n : ℝ) * K * (g.edist p q).toReal + ε := by
  let U : Set M := cstar.source ∩ cstar ⁻¹' Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r
  let u : M → ℝ := P ∘ cstar
  have hU : IsOpen U :=
    hc.continuousOn.isOpen_inter_preimage cstar.open_source Metric.isOpen_ball
  have hqU : q ∈ U := by
    refine ⟨hq, ?_⟩
    change cstar q ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r
    rw [h0]
    exact Metric.mem_ball_self hr
  have hu : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ u U := by
    dsimp only [u]
    exact (hP.contMDiff.comp_contMDiffOn hc).mono inter_subset_left
  have huq : u q = (g.edist p q).toReal := by
    simpa only [u, Function.comp_apply, h0] using hP0
  have hdist : ∀ y ∈ U, g.edist p y ≤ ENNReal.ofReal (u y) := by
    intro y hy
    have hz : ‖cstar y‖ < r := by
      have hy2 : cstar y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r := hy.2
      simpa only [Metric.mem_ball, dist_zero_right] using hy2
    have hfinz := hfinite (cstar y) hz
    have hfiny : g.edist p y ≠ (⊤ : ℝ≥0∞) := by
      simpa only [cstar.left_inv hy.1] using hfinz
    have hmaj := hmajor (cstar y) hz
    rw [cstar.left_inv hy.1] at hmaj
    have hto : ENNReal.ofReal ((g.edist p y).toReal) = g.edist p y :=
      ENNReal.ofReal_toReal hfiny
    calc
      g.edist p y = ENNReal.ofReal ((g.edist p y).toReal) := hto.symm
      _ ≤ ENNReal.ofReal (P (cstar y)) := ENNReal.ofReal_le_ofReal hmaj
      _ = ENNReal.ofReal (u y) := by rfl
  have hop := shiNormalChart_scalar_operators D hc hi hq h0 J σ hJ hd hH hP
  have hgrad' : scalarGradientSq g u q ≤ 1 := by
    rw [hop.1]
    nlinarith [norm_nonneg (fderiv ℝ P 0)]
  have htrace' : D.laplacian u q ≤
      (n : ℝ) / (g.edist p q).toReal +
        (n : ℝ) * K * (g.edist p q).toReal + ε := by
    simpa only [u, hop.2] using htrace
  exact ⟨U, u, hU, hqU, hu, huq, hdist, hgrad', htrace'⟩

theorem exists_shi_polynomial_distance_support
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (p q : M) (cstar : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (J : EuclideanSpace ℝ (Fin n) ≃L[ℝ] TangentSpace (𝓡 n) q)
    (σ : Fin n ≃ Fin (Module.finrank ℝ (TangentSpace (𝓡 n) q)))
    (hq : q ∈ cstar.source) (h0 : cstar q = 0)
    (hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
      cstar cstar.source)
    (hi : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) ∞
      cstar.symm cstar.target)
    (hJ : ∀ i, J (EuclideanSpace.basisFun (Fin n) ℝ i) =
      g.orthonormalBasis q (σ i))
    (hd : mvfderiv (𝓡 n) cstar q =
      (J.symm : TangentSpace (𝓡 n) q →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (hH : ∀ i a b, D.hessian (fun y => cstar y i) q a b = 0)
    (d R K B ρ C0 : ℝ)
    (hdistance : d = (g.edist p q).toReal)
    (hdpos : 0 < d) (hdR : d ≤ R) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hρ : 0 < ρ) (hC0 : 0 ≤ C0)
    (hfinite : ∀ z, ‖z‖ < ρ →
      g.edist p (cstar.symm z) ≠ (⊤ : ℝ≥0∞))
    (henergy : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (cseq : ℕ → ℝ)
    (L : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (Q : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hcseq : ∀ j, d ≤ cseq j ∧ cseq j ≤ R)
    (hcseqlim : Tendsto cseq atTop (𝓝 d))
    (henergy0 : ∀ j, henergy j 0 = cseq j ^ 2)
    (hL : ∀ j, ‖L j‖ ≤ 2 * cseq j)
    (hQ : ∀ j, ‖Q j‖ ≤ B)
    (hQsym : ∀ j v w, Q j v w = Q j w v)
    (htrace : ∀ j, ∑ i, Q j (EuclideanSpace.basisFun (Fin n) ℝ i)
      (EuclideanSpace.basisFun (Fin n) ℝ i) ≤
      2 * (n : ℝ) + 2 * (n : ℝ) * K * cseq j ^ 2)
    (herror : ∀ j z, ‖z‖ < ρ →
      |henergy j z - henergy j 0 - L j z - Q j z z / 2| ≤ C0 * ‖z‖ ^ 3)
    (hmajor : ∀ j z, ‖z‖ < ρ →
      (g.edist p (cstar.symm z)).toReal ≤ Real.sqrt (henergy j z))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (P : EuclideanSpace ℝ (Fin n) → ℝ) (r : ℝ),
      0 < r ∧ r ≤ ρ ∧ ContDiff ℝ ∞ P ∧
      P 0 = d ∧
      (∀ z, ‖z‖ < r →
        (g.edist p (cstar.symm z)).toReal ≤ P z) ∧
      ‖fderiv ℝ P 0‖ ≤ 1 ∧
      (∑ i, fderiv ℝ (fderiv ℝ P) 0
        (EuclideanSpace.basisFun (Fin n) ℝ i)
        (EuclideanSpace.basisFun (Fin n) ℝ i)) ≤
        (n : ℝ) / d + (n : ℝ) * K * d + ε := by
  let f : EuclideanSpace ℝ (Fin n) → ℝ := fun z =>
    (g.edist p (cstar.symm z)).toReal
  have hf0 : f 0 = d := by
    have hzero : cstar.symm 0 = q := by
      rw [← h0]
      exact cstar.left_inv hq
    simp only [f, hzero, hdistance]
  obtain ⟨P, r, hr, hrrho, hP, hP0, hPmajor, hPgrad, hPlap⟩ :=
    exists_smooth_upper_support_of_energy_expansions f henergy cseq L Q
      d R K B ρ C0 hdpos hdR hK hB hρ hC0 hf0 hcseq hcseqlim henergy0 hL hQ
      hQsym htrace herror hmajor ε hε
  refine ⟨P, r, hr, hrrho, hP, ?_, ?_, hPgrad, hPlap⟩
  · exact hP0
  · simpa only [f] using hPmajor

set_option maxHeartbeats 6000000 in

set_option synthInstance.maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency false in
theorem exists_shi_native_distance_upper_support [T2Space M]
    (D : LeviCivitaData g) (p q : M) (R K : ℝ)
    (hcompact : IsCompact (closure (g.ball p R))) (hq : q ∈ g.ball p R)
    (hd : 0 < (g.edist p q).toReal) (hK : 0 ≤ K)
    (hRm : ∀ y ∈ g.ball p R, D.curvatureTensorNorm y ≤ K)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (U : Set M) (u : M → ℝ), IsOpen U ∧ q ∈ U ∧
      ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ u U ∧ u q = (g.edist p q).toReal ∧
      (∀ y ∈ U, g.edist p y ≤ ENNReal.ofReal (u y)) ∧
      scalarGradientSq g u q ≤ 1 ∧ D.laplacian u q ≤
        (n : ℝ) / (g.edist p q).toReal +
          (n : ℝ) * K * (g.edist p q).toReal + ε := by
  classical
  let d := (g.edist p q).toReal
  have hfin : g.edist p q ≠ (⊤ : ℝ≥0∞) :=
    ne_of_lt (hq.trans ENNReal.ofReal_lt_top)
  have hdR : d < R := ENNReal.toReal_lt_of_lt_ofReal hq
  have hR : 0 < R := hd.trans hdR
  obtain ⟨m, c, C, r₀, L, B₀, hr₀, _hr₀1, hL, hB₀, hc, hi, hC,
    hCs, _himage, _hcover, hbuffer, hmetric, hGamma⟩ :=
    exists_shi_buffered_atlas D hcompact
  obtain ⟨cstar, J, σ, hqstar, hstar0, hstar, hstari, hJ, hJmetric, hJd, hH⟩ :=
    exists_shi_normal_chart D q
  obtain ⟨N, hN, _hmesh, _hshort, hframes⟩ :=
    exists_shi_uniform_bounded_parallel_frames D c C hc hi hCs hr₀ hL hB₀
      hR.le hbuffer hmetric hGamma
  let a : Fin N → ℝ := fun i => shiPathTime N i.val
  let b : Fin N → ℝ := fun i => shiPathTime N (i.val + 1)
  have hab (i : Fin N) : a i < b i := shiPathTime_step hN i.val
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have htime (k : ℕ) (hk : k ≤ N) :
      0 ≤ shiPathTime N k ∧ shiPathTime N k ≤ 1 := by
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) hNreal.le
    · exact (div_le_one hNreal).mpr (by exact_mod_cast hk)
  have ha (i : Fin N) : 0 ≤ a i := (htime i.val i.isLt.le).1
  have hb (i : Fin N) : b i ≤ 1 := (htime (i.val + 1) (Nat.succ_le_of_lt i.isLt)).2
  have hsize : ∑ i, (b i - a i) = 1 := by
    have he (i : Fin N) : b i - a i = 1 / (N : ℝ) := by
      simp only [a, b, shiPathTime, Nat.cast_add, Nat.cast_one]
      ring
    simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [ne_of_gt hNreal]
  let ce := shiPathExtendedChart c cstar
  let Ce := shiPathExtendedCore C q
  have hex (k : Sum (Fin m) Unit) :=
    shiPathExtended_data c cstar C q hC hCs hc hi hqstar hstar hstari k
  obtain ⟨ρ, B, hρ, _hρ1, hB, huniform⟩ :=
    exists_shiJoinedAtlas_uniform_bound D ce Ce (fun k => (hex k).2.2.1)
      (fun k => (hex k).2.2.2) (fun k => (hex k).1) (fun k => (hex k).2.1)
      a b hab L R hL hR.le
  obtain ⟨γ, hγ, hγball, hspeed, henergy, hlim⟩ :=
    exists_contMDiff_energy_path_sequence g hfin hdR
  have hterminal (j : ℕ) :
      ∃ Jj : V ≃L[ℝ] TangentSpace (𝓡 n) (γ j 1),
        (∀ v w, g.inner (γ j 1) (Jj v) (Jj w) = inner ℝ v w) ∧
        mvfderiv (𝓡 n) cstar (γ j 1) =
          (Jj.symm : TangentSpace (𝓡 n) (γ j 1) →L[ℝ] V) := by
    rw [(hγ j).2.1]
    exact ⟨J, hJmetric, hJd⟩
  choose Jj hJj hdj using hterminal
  have hframe (j : ℕ) := hframes (γ j) (hγ j).2.2
    (fun t ht => subset_closure (hγball j ht)) (hspeed j)
    (Jj j : V →L[ℝ] TangentSpace (𝓡 n) (γ j 1)) (hJj j)
  choose label P hinsideC hPC hPd hjoin hend hpair hPn hT _hA using hframe
  have hinside (j : ℕ) (i : Fin N) : MapsTo (γ j) (Icc (a i) (b i))
      (c (label j i)).source :=
    fun t ht => hCs (label j i) (interior_subset (hinsideC j i ht))
  have hqj (j : ℕ) : γ j 1 ∈ cstar.source := by rw [(hγ j).2.1]; exact hqstar
  have hljet (j : ℕ) (i : Fin N) := shiPathEndpoint_transition_jets D hN c cstar
    (label j) (γ j) (P j) hc hi (hinside j) hstar hstari (hqj j) (Jj j) (hdj j)
    (hjoin j) (hend j) i i.castSucc (Or.inl rfl)
  have hrjet (j : ℕ) (i : Fin N) := shiPathEndpoint_transition_jets D hN c cstar
    (label j) (γ j) (P j) hc hi (hinside j) hstar hstari (hqj j) (Jj j) (hdj j)
    (hjoin j) (hend j) i i.succ (Or.inr rfl)
  have htuple (j : ℕ) (i : Fin N) := shiPathTuple_compact_membership hN c cstar C
    hC hCs hc hi q hqstar hstar hstari (label j) (γ j) (P j) (hγ j).2.2
    (hγ j).2.1 (hinsideC j) (hPC j) hL (hPn j) (hT j) i
  have hmem (j : ℕ) (i : Fin N) (t : ℝ) (ht : t ∈ Icc (a i) (b i)) :
      shiPathTuple c cstar (label j) (γ j) (P j) i t ∈
        shiJoinedAtlasTuples ce Ce (a i) (b i) L R (Sum.inl (label j i))
          (shiPathVertexLabel (label j) i.castSucc)
          (shiPathVertexLabel (label j) i.succ) :=
    (htuple j i).2.2.2.2.2.2.2 ht
  have hdom (j : ℕ) (i : Fin N) (z : V) (hz : ‖z‖ < ρ)
      (t : ℝ) (ht : t ∈ Icc (a i) (b i)) :
      (shiPathTuple c cstar (label j) (γ j) (P j) i t, z) ∈
        shiJoinedDomain D (c (label j i))
          (shiPathVertexChart c cstar (label j) i.castSucc)
          (shiPathVertexChart c cstar (label j) i.succ) (a i) (b i) :=
    (huniform i (Sum.inl (label j i)) (shiPathVertexLabel (label j) i.castSucc)
      (shiPathVertexLabel (label j) i.succ)).1
      ⟨hmem j i t ht, by simpa only [Metric.mem_closedBall, dist_zero_right] using hz.le⟩
  let e : ℕ → Fin N → ℝ → V → ℝ := fun j i => shiActualJoinedDensity D
    (c (label j i)) (a i) (b i) ((c (label j i)) ∘ γ j) (P j i)
    (shiPathEndpoint D c cstar (label j) (γ j) (P j) i i.castSucc)
    (shiPathEndpoint D c cstar (label j) (γ j) (P j) i i.succ)
  have heq (j : ℕ) (i : Fin N) (t : ℝ) (ht : t ∈ Icc (a i) (b i)) :
      e j i t = shiJoinedDensity g D (c (label j i))
        (shiPathVertexChart c cstar (label j) i.castSucc)
        (shiPathVertexChart c cstar (label j) i.succ) (a i) (b i)
        (shiPathTuple c cstar (label j) (γ j) (P j) i t) := by
    funext z
    exact (shiPathTuple_density_eq_actual D hN c cstar (label j) (γ j) (P j)
      hc hi (hγ j).2.2 (hinside j) (hPd j) (hqj j)
      (fun i => (hljet j i).1) (fun i => (hrjet j i).1) i t ht z).symm
  have hreg (j : ℕ) (i : Fin N) := shiPathTuple_density_regular D c cstar
    (label j) (γ j) (P j) hc hi hstar hstari i ρ (htuple j i).2.2.2.2.2.2.1
    (fun t ht => (hdom j i 0 (by simpa using hρ) t ht).1) (hdom j i)
  have heC (j : ℕ) (i : Fin N) (z : V) (hz : ‖z‖ < ρ) :
      ContinuousOn (fun t => e j i t z) (Icc (a i) (b i)) :=
    ((hreg j i).1 z hz).congr (fun t ht => congrFun (heq j i t ht) z)
  have hLC (j : ℕ) (i : Fin N) :
      ContinuousOn (fun t => fderiv ℝ (e j i t) 0) (Icc (a i) (b i)) :=
    (hreg j i).2.1.congr (fun t ht => congrArg (fun f : V → ℝ => fderiv ℝ f 0)
      (heq j i t ht))
  have hQC (j : ℕ) (i : Fin N) :
      ContinuousOn (fun t => fderiv ℝ (fderiv ℝ (e j i t)) 0) (Icc (a i) (b i)) :=
    (hreg j i).2.2.congr (fun t ht => congrArg
      (fun f : V → ℝ => fderiv ℝ (fderiv ℝ f) 0) (heq j i t ht))
  have hbound (j : ℕ) := shi_integrated_energy_jets a b (e j)
    (fun i => (hab i).le) hsize ρ B hρ (heC j) (hLC j) (hQC j)
    (by
      intro i t ht
      rw [heq j i t ht]
      obtain ⟨h1, h2, hs, he⟩ := (huniform i (Sum.inl (label j i))
        (shiPathVertexLabel (label j) i.castSucc)
        (shiPathVertexLabel (label j) i.succ)).2 _ (hmem j i t ht)
      exact ⟨h1, h2, hs, fun z hz => he z hz.le⟩)
  have hcoord (j : ℕ) (i : Fin N) :=
    shiPath_coordinate_regular (hc (label j i)) (hγ j).2.2 (hab i) (hinside j i)
  have hgeo (j : ℕ) := shiActualJoinedDensity_integrated_jet_bounds D a b hab ha hb
    hsize (fun i => c (label j i)) (fun i => hc (label j i)) (fun i => hi (label j i))
    (fun i => (c (label j i)) ∘ γ j) (P j) (fun i => (hcoord j i).1)
    (fun i t ht => (c (label j i)).map_source (hinside j i ht)) (hPC j)
    (by intro i t ht; rw [(hcoord j i).2.2 t ht]; exact hPd j i t ht)
    (by
      intro i t ht v w
      simp only [Function.comp_apply]
      rw [shiChartMetric_at_source (hc (label j i)) (hi (label j i)) (hinside j i ht)]
      exact hpair j i t ht v w)
    (fun i => shiPathEndpoint D c cstar (label j) (γ j) (P j) i i.castSucc)
    (fun i => shiPathEndpoint D c cstar (label j) (γ j) (P j) i i.succ)
    (fun i => (hljet j i).2.1.of_le (WithTop.coe_le_coe.mpr le_top))
    (fun i => (hrjet j i).2.1.of_le (WithTop.coe_le_coe.mpr le_top))
    (fun i => (hljet j i).2.2.1) (fun i => (hrjet j i).2.2.1)
    (fun i => (hljet j i).2.2.2.1) (fun i => (hrjet j i).2.2.2.1)
    (by intro i v; rw [(hljet j i).2.2.2.2]; rfl)
    (by intro i v; rw [(hrjet j i).2.2.2.2]; rfl) K hK
    (by
      intro i t ht
      simp only [Function.comp_apply]
      rw [(c (label j i)).left_inv (hinside j i ht)]
      exact hRm _ (hγball j ⟨(ha i).trans ht.1, ht.2.trans (hb i)⟩))
    (hLC j) (hQC j)
  let E : ℕ → V → ℝ := fun j => shiIntegratedEnergy a b (e j)
  let Lj : ℕ → V →L[ℝ] ℝ := fun j => shiIntegratedLinearJet a b (e j)
  let Qj : ℕ → V →L[ℝ] V →L[ℝ] ℝ := fun j => shiIntegratedQuadraticJet a b (e j)
  have hEzero (j : ℕ) : E j 0 = pathEnergy g (γ j) := by
    calc
      E j 0 = ∑ i : Fin N, ∫ t in a i..b i, (pathSpeed g (γ j) t) ^ 2 := by
        change (∑ i : Fin N, ∫ t in a i..b i, e j i t 0) = _
        apply Finset.sum_congr rfl
        intro i _
        apply intervalIntegral.integral_congr
        intro t ht
        exact shiActualJoinedDensity_zero_eq_pathSpeed_sq D (hab i) (γ j) (P j i)
          _ _ (hc (label j i)) (hi (label j i)) (hγ j).2.2 (hinside j i)
          (hljet j i).2.2.1 (hrjet j i).2.2.1 t
          (by simpa only [uIcc_of_le (hab i).le] using ht)
      _ = ∑ i ∈ Finset.range N, ∫ t in shiPathTime N i..shiPathTime N (i + 1),
          (pathSpeed g (γ j) t) ^ 2 := by
        simpa only [a, b] using Fin.sum_univ_eq_sum_range
          (fun i => ∫ t in shiPathTime N i..shiPathTime N (i + 1),
            (pathSpeed g (γ j) t) ^ 2) N
      _ = pathEnergy g (γ j) := (shi_partition_integral_eq N (shiPathTime N) _ hN
        (fun i _ => shiPathTime_step hN i) (shiPathTime_zero N) (shiPathTime_last hN)
        htime ((continuous_pathSpeed g (hγ j).2.2).continuousOn.pow 2)).trans
          (pathEnergy_eq_integral_pathSpeed_sq g (γ j)).symm
  have hmajor (j : ℕ) (z : V) (hz : ‖z‖ < ρ) :
      g.edist p (cstar.symm z) ≤ ENNReal.ofReal (Real.sqrt (E j z)) := by
    have hpos (i : Fin N) (t : ℝ) := shiPathJoinedVariation_eq_position D hN c cstar
      (label j) (γ j) (P j) (hinside j) (hqj j) i (hljet j i).1 (hrjet j i).1 t z
    have htarget (i : Fin N) : MapsTo
        (fun t => shiPathJoinedVariation D c cstar (label j) (γ j) (P j) i t z)
        (Icc (a i) (b i)) (c (label j i)).target := by
      intro t ht
      change shiPathJoinedVariation D c cstar (label j) (γ j) (P j) i t z ∈ _
      rw [hpos i t]
      exact (hdom j i z hz t ht).2.2.2
    let seg : ℕ → ℝ → M := fun k => if hk : k < N then
      shiPathManifoldSegment D c cstar (label j) (γ j) (P j) ⟨k, hk⟩ z else fun _ => p
    let vertex : ℕ → M := fun k => if hk : k ≤ N then
      shiPathVertexMap D c cstar (label j) (γ j) (P j) ⟨k, Nat.lt_succ_of_le hk⟩ z else p
    have hv0 : vertex 0 = p := by
      dsimp only [vertex]
      rw [dif_pos (Nat.zero_le N)]
      change shiPathVertexMap D c cstar (label j) (γ j) (P j) 0 z = p
      rw [shiPathVertexMap_initial D hN c cstar (label j) (γ j) (P j)
        (by simpa only [a, shiPathTime_zero] using
          hinside j ⟨0, hN⟩ ⟨le_rfl, (hab ⟨0, hN⟩).le⟩) z]
      exact (hγ j).1
    have hvN : vertex N = cstar.symm z := by
      dsimp only [vertex]
      rw [dif_pos le_rfl]
      change shiPathVertexMap D c cstar (label j) (γ j) (P j) (Fin.last N) z = _
      exact shiPathVertexMap_terminal D hN c cstar (label j) (γ j) (P j) (hqj j)
        (by simpa only [(hγ j).2.1] using hstar0)
        (by
          rw [(hγ j).2.1]
          intro i u v
          change D.hessian (fun y => cstar y i) q u v = 0
          exact hH i u v) z
    have hd := edist_le_sqrt_sum_segmentPathEnergy g N (shiPathTime N) seg vertex
      (fun k _ => shiPathTime_step hN k)
      (by rw [shiPathTime_last hN, shiPathTime_zero]; ring)
      (by
        intro k hk
        simp only [seg, dif_pos hk]
        exact shiPathManifoldSegment_contMDiffOn D c cstar (label j) (γ j) (P j)
          hc hi (hγ j).2.2 (hinside j) (hPC j) ⟨k, hk⟩ z (htarget ⟨k, hk⟩))
      (by
        intro k hk
        simp only [seg, vertex, dif_pos hk, dif_pos hk.le]
        exact (shiPathManifoldSegment_endpoints D hN c cstar (label j) (γ j) (P j)
          ⟨k, hk⟩ z (hdom j ⟨k, hk⟩ z hz _ ⟨le_rfl, (hab ⟨k, hk⟩).le⟩)).1)
      (by
        intro k hk
        simp only [seg, vertex, dif_pos hk, dif_pos (Nat.succ_le_of_lt hk)]
        exact (shiPathManifoldSegment_endpoints D hN c cstar (label j) (γ j) (P j)
          ⟨k, hk⟩ z (hdom j ⟨k, hk⟩ z hz _ ⟨le_rfl, (hab ⟨k, hk⟩).le⟩)).2)
    have hE : E j z = ∑ k ∈ Finset.range N,
        segmentPathEnergy g (seg k) (shiPathTime N k) (shiPathTime N (k + 1)) := by
      rw [← Fin.sum_univ_eq_sum_range]
      change (∑ i : Fin N, ∫ t in a i..b i, e j i t z) = _
      apply Finset.sum_congr rfl
      intro i _
      simp only [seg, dif_pos i.isLt]
      exact shiActualJoinedDensity_integral_eq_segmentPathEnergy D (hc (label j i))
        (hi (label j i)) (hab i) _ _ _ _ z
        (shiPathJoinedVariation_contDiffOn D c cstar (label j) (γ j) (P j)
          hc hi (hγ j).2.2 (hinside j) (hPC j) i z) (htarget i)
    rw [hv0, hvN, ← hE] at hd
    exact hd
  let cj : ℕ → ℝ := fun j => Real.sqrt (E j 0)
  have hEpos (j : ℕ) : 0 ≤ E j 0 := (hgeo j).1
  have hcj (j : ℕ) : d ≤ cj j ∧ cj j ≤ R := by
    change d ≤ Real.sqrt (E j 0) ∧ Real.sqrt (E j 0) ≤ R
    rw [hEzero j]
    exact ⟨Real.le_sqrt_of_sq_le (henergy j).1,
      (Real.sqrt_le_sqrt (henergy j).2).trans_eq (Real.sqrt_sq hR.le)⟩
  have hcjlim : Tendsto cj atTop (𝓝 d) := by
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp hlim
    simpa only [cj, hEzero, Real.sqrt_sq hd.le, Function.comp_def, d] using h
  have hcjSq (j : ℕ) : E j 0 = cj j ^ 2 := (Real.sq_sqrt (hEpos j)).symm
  let f : V → ℝ := fun z => (g.edist p (cstar.symm z)).toReal
  have hf0 : f 0 = d := by
    have hiq : cstar.symm 0 = q := by rw [← hstar0]; exact cstar.left_inv hqstar
    simp only [f, hiq, d]
  obtain ⟨Q, r, hr, hrρ, hQ, hQ0, hQmajor, hQgrad, hQtrace⟩ :=
    exists_smooth_upper_support_of_energy_expansions f E cj Lj Qj d R K B ρ B
      hd hdR.le hK (zero_le_one.trans hB) hρ (zero_le_one.trans hB) hf0 hcj hcjlim hcjSq
      (fun j => (hgeo j).2.1) (fun j => (hbound j).2.1) (fun j => (hbound j).2.2.1)
      (by intro j; simpa only [← hcjSq j] using (hgeo j).2.2)
      (fun j => (hbound j).2.2.2)
      (fun j z hz => ENNReal.toReal_le_of_le_ofReal (Real.sqrt_nonneg _) (hmajor j z hz)) ε hε
  exact shi_pullback_energy_support g D p q cstar J σ hqstar hstar0 hstar hstari hJ hJd hH
    r hr Q hQ hQ0
    (fun z hz => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hmajor 0 z (hz.trans_le hrρ)))
    hQmajor hQgrad K ε hQtrace

end PoincareConjecture.M04
