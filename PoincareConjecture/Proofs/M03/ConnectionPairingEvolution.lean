import PoincareConjecture.Proofs.M03.MetricGradientEvolution









set_option autoImplicit false
set_option maxHeartbeats 1800000

open scoped Manifold ContDiff Bundle Topology
open Set

universe u

namespace PoincareConjecture.Proofs.M03

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem hasDerivAt_ricciFlow_koszul_pairing
    {J : Set ℝ} (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J)
    {U : Set M} (hU : IsOpen U)
    (X Y Z : (x : M) → TangentSpace (𝓡 n) x)
    (hX : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U)
    (hZ : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) U)
    {x : M} (hx : x ∈ U) :
    let c := extChartAt (𝓡 n) x
    let q := fun y (u v : TangentSpace (𝓡 n) y) =>
      -2 * (F.connection t).ricci y u v
    let d := fun (V W : (y : M) → TangentSpace (𝓡 n) y)
        (a : EuclideanSpace ℝ (Fin n)) =>
      fderiv ℝ (fun z => q (c.symm z) (V (c.symm z)) (W (c.symm z)))
        (c x) a
    HasDerivAt
      (fun s => 2 * (F.metric s).inner x
        ((F.connection s).connection Y x (X x)) (Z x))
      (d Y Z (X x) + d Z X (Y x) - d X Y (Z x) +
        q x (VectorField.mlieBracket (𝓡 n) X Y x) (Z x) -
        q x (Y x) (VectorField.mlieBracket (𝓡 n) X Z x) -
        q x (X x) (VectorField.mlieBracket (𝓡 n) Y Z x)) t := by
  dsimp only
  let c := extChartAt (𝓡 n) x
  let q := fun y (u v : TangentSpace (𝓡 n) y) =>
    -2 * (F.connection t).ricci y u v
  let d := fun (V W : (y : M) → TangentSpace (𝓡 n) y)
      (a : EuclideanSpace ℝ (Fin n)) =>
    fderiv ℝ (fun z => q (c.symm z) (V (c.symm z)) (W (c.symm z)))
      (c x) a
  have hcx : c x ∈ c.target := mem_extChartAt_target x
  have hcsymm : c.symm (c x) = x := c.left_inv (mem_extChartAt_source x)
  have htime_mem : interior J ∈ 𝓝 t := isOpen_interior.mem_nhds ht
  have hc (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ c.target) :
      ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) ∞ c.symm z :=
    (contMDiffOn_extChartAt_symm (I := 𝓡 n) x).contMDiffAt
      (extChartAt_target_mem_nhds' hz)
  have hchart (s : ℝ) (hs : s ∈ interior J)
      (A B : (y : M) → TangentSpace (𝓡 n) y)
      (hA : ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% A) U)
      (hB : ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% B) U)
      (a : EuclideanSpace ℝ (Fin n)) :
      fderiv ℝ (fun z => (F.metric s).inner (c.symm z)
        (A (c.symm z)) (B (c.symm z))) (c x) a =
        mvfderiv (𝓡 n) (fun y => (F.metric s).inner y (A y) (B y)) x a := by
    have hpair := contMDiffOn_family_metric_pair F.smooth A B hA hB
    have hpair' := hpair.mono
      (show interior J ×ˢ U ⊆ J ×ˢ U from fun _ hp =>
        ⟨interior_subset hp.1, hp.2⟩)
    have hp := (hpair' (s, x) ⟨hs, hx⟩).contMDiffAt
      ((isOpen_interior.prod hU).mem_nhds ⟨hs, hx⟩)
    let f : M → ℝ := fun y => (F.metric s).inner y (A y) (B y)
    have hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x := by
      have hh := hp.comp x
        (contMDiffAt_const.prodMk contMDiffAt_id)
      simpa only [Function.comp_def, f] using hh
    have heid : mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n)
        c.symm (c x) = ContinuousLinearMap.id ℝ
          (TangentSpace (𝓡 n) (c x)) := by
      simpa only [(𝓡 n).range_eq_univ, mfderivWithin_univ] using
        (mfderivWithin_range_extChartAt_symm (I := 𝓡 n) (x := x))
    have hdf : fderiv ℝ (fun z => f (c.symm z)) (c x) =
        mvfderiv (𝓡 n) f x := by
      rw [← mfderiv_eq_fderiv]
      change mvfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        (f ∘ c.symm) (c x) = _
      have hf' : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f (c.symm (c x)) := by
        simpa [hcsymm] using hf.mdifferentiableAt (by simp)
      rw [mvfderiv_comp (c x) hf'
        ((hc (c x) hcx).mdifferentiableAt (by simp)), heid]
      change mvfderiv (𝓡 n) f (c.symm (c x)) = mvfderiv (𝓡 n) f x
      rw [hcsymm]
    have hdf' := congrArg (fun L => L a) hdf
    change (fderiv ℝ (fun z => (F.metric s).inner (c.symm z)
      (A (c.symm z)) (B (c.symm z))) (c x)) a =
      (mvfderiv (𝓡 n) (fun y => (F.metric s).inner y (A y) (B y)) x) a
    exact hdf'
  have hterm (B C : (y : M) → TangentSpace (𝓡 n) y)
      (hB : ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% B) U)
      (hC : ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% C) U)
      (a : EuclideanSpace ℝ (Fin n)) :
      HasDerivAt (fun s => mvfderiv (𝓡 n)
        (fun y => (F.metric s).inner y (B y) (C y)) x a)
        (d B C a) t := by
    have hg := hasDerivAt_ricciFlow_metric_spatial_derivative F ht hU B C hB
      hC x hcx (by rw [hcsymm]; exact hx) a
    have heq : (fun s => fderiv ℝ (fun z => (F.metric s).inner
        (c.symm z) (B (c.symm z)) (C (c.symm z))) (c x) a) =ᶠ[𝓝 t]
        (fun s => mvfderiv (𝓡 n) (fun y => (F.metric s).inner y (B y) (C y)) x a) := by
      filter_upwards [htime_mem] with s hs
      exact hchart s hs B C hB hC a
    change HasDerivAt (fun s => fderiv ℝ (fun z => (F.metric s).inner
      (c.symm z) (B (c.symm z)) (C (c.symm z))) (c x) a)
      _ t at hg
    have hg' := hg.congr_of_eventuallyEq heq.symm
    simpa [d, q, c] using hg'
  have hYZ := hterm Y Z hY hZ (X x)
  have hZX := hterm Z X hZ hX (Y x)
  have hXY := hterm X Y hX hY (Z x)
  have hbr (u v : TangentSpace (𝓡 n) x) :
      HasDerivAt (fun s => (F.metric s).inner x
        u v) (q x u v) t := by
    have he := (F.equation t (interior_subset ht) x
      u v).hasDerivAt
      (mem_interior_iff_mem_nhds.mp ht)
    simpa [q] using he
  have hbrXY := hbr (VectorField.mlieBracket (𝓡 n) X Y x) (Z x)
  have hbrXZ := hbr (Y x) (VectorField.mlieBracket (𝓡 n) X Z x)
  have hbrYZ := hbr (X x) (VectorField.mlieBracket (𝓡 n) Y Z x)
  have hsum := (((((hYZ.add hZX).sub hXY).add hbrXY).sub hbrXZ).sub hbrYZ)
  have hkoszul :
      (fun s => 2 * (F.metric s).inner x
        ((F.connection s).connection Y x (X x)) (Z x)) =ᶠ[𝓝 t]
      (fun s =>
        mvfderiv (𝓡 n) (fun y => (F.metric s).inner y (Y y) (Z y)) x (X x) +
        mvfderiv (𝓡 n) (fun y => (F.metric s).inner y (Z y) (X y)) x (Y x) -
        mvfderiv (𝓡 n) (fun y => (F.metric s).inner y (X y) (Y y)) x (Z x) +
        (F.metric s).inner x (VectorField.mlieBracket (𝓡 n) X Y x) (Z x) -
        (F.metric s).inner x (Y x) (VectorField.mlieBracket (𝓡 n) X Z x) -
        (F.metric s).inner x (X x) (VectorField.mlieBracket (𝓡 n) Y Z x)) := by
    filter_upwards [htime_mem] with s hs
    have hk := (F.connection s).koszul X Y Z
      ((hX.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))
      ((hY.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))
      ((hZ.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))
    simpa only [Function.comp_def] using hk
  apply hsum.congr_of_eventuallyEq hkoszul

end PoincareConjecture.Proofs.M03
