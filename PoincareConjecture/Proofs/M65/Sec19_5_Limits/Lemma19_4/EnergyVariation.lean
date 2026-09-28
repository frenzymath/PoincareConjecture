import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.FluxRegularity










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle BigOperators Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

set_option maxHeartbeats 1000000 in



theorem m65PlaneColumn_contMDiffAt (u : ℝ → LoopPlane → M)
    {t : ℝ} {z : LoopPlane}
    (hu : ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 n) 2 (Function.uncurry u) (t, z))
    (i : Fin 2) :
    ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 2)) ((𝓡 n).prod (𝓡 n)) 1
      (fun p : ℝ × LoopPlane => (⟨u p.1 p.2,
        mfderiv (𝓡 2) (𝓡 n) (u p.1) p.2 (EuclideanSpace.basisFun (Fin 2) ℝ i)⟩ :
          TangentBundle (𝓡 n) M)) (t, z) := by
  have hp : ContMDiffAt (((𝓘(ℝ, ℝ)).prod (𝓡 2)).prod (𝓡 2)) (𝓡 n) 2
      (Function.uncurry (fun p : ℝ × LoopPlane => u p.1)) ((t, z), z) :=
    hu.comp ((t, z), z) (contMDiffAt_fst.fst.prodMk contMDiffAt_snd)
  have hcoord := hp.mfderiv (fun p : ℝ × LoopPlane => u p.1) Prod.snd (m := 1)
    contMDiffAt_snd (by norm_num)
  have hv : ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 2)) ((𝓡 2).prod (𝓡 2)) 1
      (fun p : ℝ × LoopPlane => (⟨p.2, EuclideanSpace.basisFun (Fin 2) ℝ i⟩ :
        TangentBundle (𝓡 2) LoopPlane)) (t, z) := by
    rw [Bundle.contMDiffAt_totalSpace]
    exact ⟨contMDiffAt_snd, by simpa using contMDiffAt_const⟩
  exact ContMDiffAt.clm_apply_of_inCoordinates
    (IB₁ := 𝓡 2) (IB₂ := 𝓡 n) (IM := (𝓘(ℝ, ℝ)).prod (𝓡 2))
    (E₁ := TangentSpace (𝓡 2)) (E₂ := TangentSpace (𝓡 n))
    (b₁ := Prod.snd) (b₂ := Function.uncurry u)
    (ϕ := fun p : ℝ × LoopPlane => mfderiv (𝓡 2) (𝓡 n) (u p.1) p.2)
    (v := fun _ => EuclideanSpace.basisFun (Fin 2) ℝ i)
    hcoord hv (hu.of_le (by norm_num))

variable {a b : ℝ} (F : RicciFlow n M (Icc a b))



theorem m65MovingEnergyDensity_contDiffAt (u : ℝ → LoopPlane → M)
    {t : ℝ} {z : LoopPlane} (ht : t ∈ Ioo a b)
    (hu : ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 n) 2 (Function.uncurry u) (t, z)) :
    ContDiffAt ℝ 1 (fun p : ℝ × LoopPlane => m60EnergyDensity (F.metric p.1) (u p.1) p.2)
      (t, z) := by
  have hdomain : Icc a b ×ˢ (univ : Set M) ∈ 𝓝 (t, u t z) :=
    prod_mem_nhds (Icc_mem_nhds ht.1 ht.2) univ_mem
  have hmetric := ((F.smooth.contMDiffAt hdomain).of_le
    (show (1 : WithTop ℕ∞) ≤ ∞ from by simp)).comp (t, z)
      (contMDiffAt_fst.prodMk (hu.of_le (by norm_num)))
  have hpair (i : Fin 2) : ContDiffAt ℝ 1
      (fun p : ℝ × LoopPlane => (F.metric p.1).inner (u p.1 p.2)
        (mfderiv (𝓡 2) (𝓡 n) (u p.1) p.2 (EuclideanSpace.basisFun (Fin 2) ℝ i))
        (mfderiv (𝓡 2) (𝓡 n) (u p.1) p.2 (EuclideanSpace.basisFun (Fin 2) ℝ i)))
      (t, z) := by
    have hcol := m65PlaneColumn_contMDiffAt u hu i
    have h := hmetric.clm_bundle_apply₂ (F₃ := ℝ) (E₃ := Bundle.Trivial M ℝ) hcol hcol
    have hh := (Bundle.contMDiffAt_totalSpace.mp h).2
    simp only [Bundle.Trivial.fiberBundle_trivializationAt', Bundle.Trivial.trivialization_apply]
      at hh
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hh
    exact contMDiffAt_iff_contDiffAt.mp hh
  have h := contDiffAt_const.mul ((hpair 0).add (hpair 1))
    (f := fun _ : ℝ × LoopPlane => (1 / 2 : ℝ))
  simpa only [m60EnergyDensity, Matrix.trace, Fin.sum_univ_two, Matrix.diag_apply,
    m60AreaGram] using h



theorem m65MovingEnergyDensity_hasDerivAt (u : ℝ → LoopPlane → M)
    {t : ℝ} {z : LoopPlane} (ht : t ∈ Ioo a b)
    (hu : ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 n) 2 (Function.uncurry u) (t, z)) :
    HasDerivAt (fun s => m60EnergyDensity (F.metric s) (u s) z)
      (-(∑ i : Fin 2, (F.connection t).ricci (u t z)
        (mfderiv (𝓡 2) (𝓡 n) (u t) z (EuclideanSpace.basisFun (Fin 2) ℝ i))
        (mfderiv (𝓡 2) (𝓡 n) (u t) z (EuclideanSpace.basisFun (Fin 2) ℝ i))) +
      ∑ i : Fin 2, (F.metric t).inner (u t z)
        (rampHorizontalCovariantDerivative (F.connection t) (fun s => u s z)
          (fun s => mfderiv (𝓡 2) (𝓡 n) (u s) z
            (EuclideanSpace.basisFun (Fin 2) ℝ i)) t)
        (mfderiv (𝓡 2) (𝓡 n) (u t) z (EuclideanSpace.basisFun (Fin 2) ℝ i))) t := by
  let e : (s : ℝ) → Fin 2 → TangentSpace (𝓡 n) (u s z) := fun s i =>
    mfderiv (𝓡 2) (𝓡 n) (u s) z (EuclideanSpace.basisFun (Fin 2) ℝ i)
  let A : Fin 2 → TangentSpace (𝓡 n) (u t z) := fun i =>
    rampHorizontalCovariantDerivative (F.connection t) (fun s => u s z) (fun s => e s i) t
  have hbase := (hu.of_le (show (1 : WithTop ℕ∞) ≤ 2 from by norm_num)).comp t
    (contMDiffAt_id.prodMk contMDiffAt_const)
  have hcol (i : Fin 2) := (m65PlaneColumn_contMDiffAt u hu i).comp t
    (contMDiffAt_id.prodMk contMDiffAt_const)
  have hpair (i : Fin 2) := M62.hasDerivAt_flow_metric_pairing F ht
    (hbase.mdifferentiableAt (by decide))
    ((hcol i).mdifferentiableAt (by decide)) ((hcol i).mdifferentiableAt (by decide))
  have h := ((hpair 0).add (hpair 1)).const_mul (1 / 2 : ℝ)
  convert! h using 1
  · funext s
    simp only [m60EnergyDensity, Matrix.trace, Fin.sum_univ_two, Matrix.diag_apply,
      m60AreaGram, Function.comp_def, Function.uncurry_apply_pair, id_eq, Pi.add_apply]
  · let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric t).toRiemannianMetric⟩
    have hsymm (i : Fin 2) : (F.metric t).inner (u t z) (e t i) (A i) =
        (F.metric t).inner (u t z) (A i) (e t i) := real_inner_comm (A i) (e t i)
    change -(∑ i, (F.connection t).ricci (u t z) (e t i) (e t i)) +
      (∑ i, (F.metric t).inner (u t z) (A i) (e t i)) =
        (1 / 2 : ℝ) *
          ((-2 * (F.connection t).ricci (u t z) (e t 0) (e t 0) +
            (F.metric t).inner (u t z) (A 0) (e t 0) +
            (F.metric t).inner (u t z) (e t 0) (A 0)) +
          (-2 * (F.connection t).ricci (u t z) (e t 1) (e t 1) +
            (F.metric t).inner (u t z) (A 1) (e t 1) +
            (F.metric t).inner (u t z) (e t 1) (A 1)))
    rw [hsymm 0, hsymm 1]
    simp only [Fin.sum_univ_two]
    ring

end PoincareConjecture
