import PoincareConjecture.Proofs.M03.ScalarEnergyComparison
import PoincareConjecture.Proofs.M03.CurvatureRicciDerivative
import PoincareConjecture.Proofs.M03.ConnectionNativeTime

set_option autoImplicit false

open scoped BigOperators

namespace PoincareConjecture.Proofs.M03

universe u

theorem curvature_flux_divergence_sum_reassociate
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (d : ι → ℝ) (Gamma : ι → ι → ι → ℝ)
    (uFlux : ι → ι → ι → ι → ι → ℝ)
    (l j k m : ι) :
    ∑ i, (d i +
      (∑ p : ι, (Gamma i p i * uFlux p l j k m +
        Gamma i p l * uFlux i p j k m -
        Gamma i j p * uFlux i l p k m -
        Gamma i k p * uFlux i l j p m -
        Gamma i m p * uFlux i l j k p))) =
      ∑ i, (d i + (∑ p : ι, (Gamma i p i * uFlux p l j k m +
        Gamma i p l * uFlux i p j k m -
        Gamma i j p * uFlux i l p k m -
        Gamma i k p * uFlux i l j p m -
        Gamma i m p * uFlux i l j k p))) := by
  apply Finset.sum_congr rfl
  intro i hi
  ring

open scoped Manifold ContDiff Bundle Topology
open Bundle Manifold Set

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

set_option maxHeartbeats 1200000 in

theorem curvature_iterated_lowered_frame_coordinate_derivative
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (x0 : M) :
    let V := EuclideanSpace ℝ (Fin n)
    let c := chartAt V x0
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let cb := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let E := e.localFrame cb
    let theta := e.localFrameCoeff (𝓡 n) cb
    let Gamma := fun (x : M) (i j l : Fin n) =>
      theta l x (D.connection (E j) x (E i x))
    let L := fun (r : ℕ) (alpha : Fin (r + 4) → Fin n) (z : V) =>
      g.inner (c.symm z)
        (curvatureOnFields_iteratedCovariantDerivative D r
          (fun j : Fin (r + 3) => E (alpha j.castSucc)) (c.symm z))
        (E (alpha (Fin.last (r + 3))) (c.symm z))
    ∀ (r : ℕ) (z : V), z ∈ c.target →
      ∀ (i : Fin n) (alpha : Fin (r + 4) → Fin n),
        fderiv ℝ (L r alpha) z (EuclideanSpace.single i 1) =
          L (r + 1) (Fin.cons i alpha) z +
            ∑ j : Fin (r + 4), ∑ p : Fin n,
              Gamma (c.symm z) i (alpha j) p *
                L r (Function.update alpha j p) z := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  dsimp only
  let V := EuclideanSpace ℝ (Fin n)
  let c := chartAt V x0
  let e := trivializationAt V (TangentSpace (𝓡 n)) x0
  let cb := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let E := e.localFrame cb
  let theta := e.localFrameCoeff (𝓡 n) cb
  let N := fun (P A : (y : M) → TangentSpace (𝓡 n) y) y =>
    D.connection A y (P y)
  let K := curvatureOnFields_iteratedCovariantDerivative D
  let low := fun r (Z : Fin (r + 4) → (y : M) → TangentSpace (𝓡 n) y) y =>
    g.inner y (K r (Fin.init Z) y) (Z (Fin.last (r + 3)) y)
  let Gamma := fun (x : M) (i j l : Fin n) => theta l x (N (E i) (E j) x)
  let L := fun (r : ℕ) (alpha : Fin (r + 4) → Fin n) (z : V) =>
    low r (fun j => E (alpha j)) (c.symm z)
  change ∀ (r : ℕ) (z : V), z ∈ c.target →
    ∀ (i : Fin n) (alpha : Fin (r + 4) → Fin n),
      fderiv ℝ (L r alpha) z (EuclideanSpace.single i 1) =
        L (r + 1) (Fin.cons i alpha) z +
          ∑ j : Fin (r + 4), ∑ p : Fin n,
            Gamma (c.symm z) i (alpha j) p *
              L r (Function.update alpha j p) z
  let S := fun W : (y : M) → TangentSpace (𝓡 n) y =>
    ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% W) e.baseSet
  have hE (i : Fin n) : S (E i) :=
    e.contMDiffOn_localFrame_baseSet (I := 𝓡 n) ∞ cb i
  have hN (P A : (y : M) → TangentSpace (𝓡 n) y) (hP : S P) (hA : S A) :
      S (N P A) := D.contMDiffOn_connection_apply e.open_baseSet P A hP hA
  have hK (r : ℕ) (Z : Fin (r + 3) → (y : M) → TangentSpace (𝓡 n) y)
      (hZ : ∀ j, S (Z j)) : S (K r Z) :=
    contMDiffOn_curvatureOnFields_iteratedCovariantDerivative D e.open_baseSet r Z hZ
  have hlow (r : ℕ) (Z : Fin (r + 4) → (y : M) → TangentSpace (𝓡 n) y)
      (hZ : ∀ j, S (Z j)) :
      ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (low r Z) e.baseSet :=
    (hK r (Fin.init Z) (fun j => hZ j.castSucc)).inner_bundle (hZ (Fin.last (r + 3)))
  have hrec (W : (y : M) → TangentSpace (𝓡 n) y)
      {x : M} (hx : x ∈ e.baseSet) : W x = ∑ p, theta p x (W x) • E p x :=
    e.eq_sum_localFrameCoeff_smul (I := 𝓡 n) (b := cb) hx
  have hslot (r : ℕ) {x : M} (hx : x ∈ e.baseSet)
      (Z : Fin (r + 3) → (y : M) → TangentSpace (𝓡 n) y) (hZ : ∀ j, S (Z j))
      (j : Fin (r + 3)) (W : (y : M) → TangentSpace (𝓡 n) y) (hW : S W) :
      K r (Function.update Z j W) x =
        ∑ p, theta p x (W x) • K r (Function.update Z j (E p)) x := by
    obtain ⟨A, hA⟩ := exists_curvatureOnFields_iteratedCovariantDerivative_multilinearMap D r x
    have hev (W' : (y : M) → TangentSpace (𝓡 n) y) (hW' : S W') :
        A (Function.update (fun l => Z l x) j (W' x)) = K r (Function.update Z j W') x := by
      have he : (fun l => Function.update Z j W' l x) =
          Function.update (fun l => Z l x) j (W' x) := by
        funext l
        by_cases hl : l = j
        · subst l
          simp only [Function.update_self]
        · simp only [Function.update_of_ne hl]
      rw [← he]
      apply hA e.open_baseSet _ _ hx
      intro l
      by_cases hl : l = j
      · subst l
        simpa only [Function.update_self] using hW'
      · simpa only [Function.update_of_ne hl] using hZ l
    calc
      _ = A (Function.update (fun l => Z l x) j (W x)) := (hev W hW).symm
      _ = A (Function.update (fun l => Z l x) j (∑ p, theta p x (W x) • E p x)) :=
        congrArg (fun v => A (Function.update (fun l => Z l x) j v)) (hrec W hx)
      _ = ∑ p, theta p x (W x) • A (Function.update (fun l => Z l x) j (E p x)) := by
        rw [A.map_update_sum]
        simp only [A.map_update_smul]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro p _
        rw [hev (E p) (hE p)]
  have hlowSlot (r : ℕ) {x : M} (hx : x ∈ e.baseSet)
      (Z : Fin (r + 4) → (y : M) → TangentSpace (𝓡 n) y) (hZ : ∀ j, S (Z j))
      (j : Fin (r + 4)) (W : (y : M) → TangentSpace (𝓡 n) y) (hW : S W) :
      low r (Function.update Z j W) x =
        ∑ p, theta p x (W x) * low r (Function.update Z j (E p)) x := by
    refine Fin.lastCases ?_ (fun l => ?_) j
    · simp only [low, Fin.init_update_last, Function.update_self]
      have hh := congrArg (g.inner x (K r (Fin.init Z) x)) (hrec W hx)
      simpa only [map_sum, map_smul, smul_eq_mul] using hh
    · simp only [low, Fin.init_update_castSucc,
        Function.update_of_ne (Fin.castSucc_ne_last l).symm]
      rw [hslot r hx (Fin.init Z) (fun s => hZ s.castSucc) l W hW]
      simp only [map_sum, sum_apply, map_smul, smul_apply, smul_eq_mul]
  have hchart (f : M → ℝ)
      (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f e.baseSet)
      {z : V} (hz : z ∈ c.target) (i : Fin n) :
      fderiv ℝ (fun w => f (c.symm w)) z (EuclideanSpace.single i 1) =
        mvfderiv (𝓡 n) f (c.symm z) (E i (c.symm z)) := by
    have hx : c.symm z ∈ e.baseSet := by
      simpa only [e, TangentBundle.trivializationAt_baseSet] using c.map_target hz
    have hcs : MDifferentiableAt 𝓘(ℝ, V) (𝓡 n) c.symm z :=
      ((contMDiffOn_chart_symm (I := 𝓡 n) (n := ∞) (x := x0)).contMDiffAt
        (c.open_target.mem_nhds hz)).mdifferentiableAt (by simp)
    have he : e.symmL ℝ (c.symm z) = mfderiv 𝓘(ℝ, V) (𝓡 n) c.symm z := by
      have hh := TangentBundle.symmL_trivializationAt (I := 𝓡 n) (x₀ := x0)
        (c.map_target hz)
      simp only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
        modelWithCornersSelf_coe_symm, Function.comp_def, id_eq, Set.range_id,
        mfderivWithin_univ] at hh
      change e.symmL ℝ (c.symm z) = mfderiv 𝓘(ℝ, V) (𝓡 n) c.symm
        (c (c.symm z)) at hh
      rwa [c.right_inv hz] at hh
    have hframe : E i (c.symm z) = e.symmL ℝ (c.symm z) (EuclideanSpace.single i 1) := by
      calc
        _ = e.basisAt cb hx i := e.localFrame_apply_of_mem_baseSet cb hx
        _ = e.symm (c.symm z) (EuclideanSpace.single i 1) := by
          simp only [Trivialization.basisAt, Module.Basis.map_apply, cb,
            OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
            Trivialization.linearEquivAt_symm_apply]
        _ = _ := (e.symmL_apply hx _).symm
    rw [hframe, ← mfderiv_eq_fderiv]
    change mvfderiv 𝓘(ℝ, V) (f ∘ c.symm) z (EuclideanSpace.single i 1) = _
    erw [mvfderiv_comp_apply z
      ((hf.contMDiffAt (e.open_baseSet.mem_nhds hx)).mdifferentiableAt (by simp))
      hcs (EuclideanSpace.single i 1), ← he]
    rfl
  intro r z hz i alpha
  let x := c.symm z
  have hx : x ∈ e.baseSet := by
    simpa only [x, e, TangentBundle.trivializationAt_baseSet] using c.map_target hz
  let Z : Fin (r + 4) → (y : M) → TangentSpace (𝓡 n) y := fun j => E (alpha j)
  have hZ (j : Fin (r + 4)) : S (Z j) := hE (alpha j)
  have hinit : Fin.init (Fin.cons (α := fun _ : Fin (r + 5) =>
      (y : M) → TangentSpace (𝓡 n) y) (E i) Z) =
      Fin.cons (α := fun _ : Fin (r + 4) => (y : M) → TangentSpace (𝓡 n) y)
        (E i) (Fin.init Z) := by
    funext j
    refine Fin.cases ?_ (fun l => ?_) j
    · rfl
    · simp only [Fin.init, Fin.castSucc_succ, Fin.cons_succ]
  have hnext : low (r + 1) (Fin.cons (E i) Z) x =
      g.inner x (K (r + 1) (Fin.cons (E i) (Fin.init Z)) x)
        (Z (Fin.last (r + 3)) x) := by
    simp only [low, hinit, Fin.cons_last]
  have hd := lower_covariant_derivative_iterated_inner D e.open_baseSet r
    (E i) Z (hE i) hZ hx
  change mvfderiv (𝓡 n) (low r Z) x (E i x) -
    (∑ j, low r (Function.update Z j (N (E i) (Z j))) x) =
      g.inner x (K (r + 1) (Fin.cons (E i) (Fin.init Z)) x)
        (Z (Fin.last (r + 3)) x) at hd
  rw [← hnext] at hd
  have hup (j : Fin (r + 4)) (p : Fin n) :
      Function.update Z j (E p) = (fun l => E (Function.update alpha j p l)) := by
    funext l
    by_cases hl : l = j
    · subst l
      simp only [Function.update_self]
    · simp only [Function.update_of_ne hl]
      rfl
  have hcons : (fun j : Fin (r + 5) =>
      E (Fin.cons (α := fun _ : Fin (r + 5) => Fin n) i alpha j)) =
      Fin.cons (α := fun _ : Fin (r + 5) => (y : M) → TangentSpace (𝓡 n) y)
        (E i) Z := by
    funext j
    refine Fin.cases ?_ (fun l => ?_) j
    · rfl
    · simp only [Fin.cons_succ]
      rfl
  have hfirst : fderiv ℝ (L r alpha) z (EuclideanSpace.single i 1) =
      mvfderiv (𝓡 n) (low r Z) x (E i x) := hchart _ (hlow r Z hZ) hz i
  have hsecond : mvfderiv (𝓡 n) (low r Z) x (E i x) =
      low (r + 1) (Fin.cons (E i) Z) x +
        ∑ j, low r (Function.update Z j (N (E i) (Z j))) x :=
    sub_eq_iff_eq_add.mp hd
  have hthird : low (r + 1) (Fin.cons (E i) Z) x =
      L (r + 1) (Fin.cons i alpha) z := by
    dsimp only [L]
    rw [hcons]
  have hfourth : (∑ j, low r (Function.update Z j (N (E i) (Z j))) x) =
      ∑ j : Fin (r + 4), ∑ p : Fin n,
        Gamma x i (alpha j) p * L r (Function.update alpha j p) z := by
    apply Finset.sum_congr rfl
    intro j _
    rw [hlowSlot r hx Z hZ j (N (E i) (Z j)) (hN _ _ (hE i) (hZ j))]
    apply Finset.sum_congr rfl
    intro p _
    rw [hup]
  exact hfirst.trans (hsecond.trans (congrArg₂ (· + ·) hthird hfourth))

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem hasDerivAt_ricciFlow_connection_frame_coordinates
    {J : Set ℝ} (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J)
    (x0 : M) :
    let V := EuclideanSpace ℝ (Fin n)
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let cb := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let E := e.localFrame cb
    let theta := e.localFrameCoeff (𝓡 n) cb
    let Gamma := fun (s : ℝ) (x : M) (i j l : Fin n) =>
      theta l x ((F.connection s).connection (E j) x (E i x))
    let G := fun x : M => ContinuousLinearMap.inCoordinates V
      (TangentSpace (𝓡 n)) (V →L[ℝ] ℝ)
      (fun y => TangentSpace (𝓡 n) y →L[ℝ] ℝ)
      x0 x x0 x ((F.metric t).inner x)
    let H := fun (x : M) (i j : Fin n) =>
      (G x).inverse (EuclideanSpace.proj j) i
    let L := fun (alpha : Fin 5 → Fin n) (x : M) =>
      (F.metric t).inner x
        (curvatureOnFields_iteratedCovariantDerivative (F.connection t) 1
          (fun j : Fin 4 => E (alpha j.castSucc)) x)
        (E (alpha (Fin.last 4)) x)
    ∀ x ∈ e.baseSet, ∀ i j l : Fin n,
      HasDerivAt (fun s => Gamma s x i j l)
        (∑ v : Fin n, H x l v *
          (-(∑ p : Fin n, ∑ q : Fin n, H x p q * L ![i,p,j,v,q] x) -
            (∑ p : Fin n, ∑ q : Fin n, H x p q * L ![j,p,v,i,q] x) +
            ∑ p : Fin n, ∑ q : Fin n, H x p q * L ![v,p,i,j,q] x)) t := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric 0).toRiemannianMetric⟩
  dsimp only
  let V := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt V (TangentSpace (𝓡 n)) x0
  let cb := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let E := e.localFrame cb
  let theta := e.localFrameCoeff (𝓡 n) cb
  let N := fun s (i j : Fin n) (x : M) =>
    (F.connection s).connection (E j) x (E i x)
  let Gamma := fun (s : ℝ) (x : M) (i j l : Fin n) => theta l x (N s i j x)
  let G := fun x : M => ContinuousLinearMap.inCoordinates V
    (TangentSpace (𝓡 n)) (V →L[ℝ] ℝ)
    (fun y => TangentSpace (𝓡 n) y →L[ℝ] ℝ)
    x0 x x0 x ((F.metric t).inner x)
  let H := fun (x : M) (i j : Fin n) =>
    (G x).inverse (EuclideanSpace.proj j) i
  let L := fun (alpha : Fin 5 → Fin n) (x : M) =>
    (F.metric t).inner x
      (curvatureOnFields_iteratedCovariantDerivative (F.connection t) 1
        (fun j : Fin 4 => E (alpha j.castSucc)) x)
      (E (alpha (Fin.last 4)) x)
  change ∀ x ∈ e.baseSet, ∀ i j l : Fin n,
    HasDerivAt (fun s => Gamma s x i j l)
      (∑ v : Fin n, H x l v *
        (-(∑ p : Fin n, ∑ q : Fin n, H x p q * L ![i,p,j,v,q] x) -
          (∑ p : Fin n, ∑ q : Fin n, H x p q * L ![j,p,v,i,q] x) +
          ∑ p : Fin n, ∑ q : Fin n, H x p q * L ![v,p,i,j,q] x)) t
  have hE (i : Fin n) : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞
      (T% (E i)) e.baseSet := e.contMDiffOn_localFrame_baseSet (I := 𝓡 n) ∞ cb i
  intro x hx i j l
  have htheta (v : TangentSpace (𝓡 n) x) :
      theta l x v = (e.continuousLinearMapAt ℝ x v) l := by
    have hh := e.localFrameCoeff_apply_of_mem_baseSet (I := 𝓡 n) cb hx
      (FiberBundle.extend V v) l
    rw [FiberBundle.extend_apply_self] at hh
    change theta l x v = _ at hh
    rw [hh]
    simp only [Trivialization.basisAt, Module.Basis.map_repr, LinearEquiv.symm_symm,
      LinearEquiv.trans_apply, cb, OrthonormalBasis.coe_toBasis_repr_apply,
      Trivialization.linearEquivAt_apply]
    rw [Trivialization.continuousLinearMapAt_apply_of_mem ℝ e hx]
    rfl
  have hN : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n))
      ((𝓡 n).prod 𝓘(ℝ, V)) ∞
      (fun p : ℝ × M => TotalSpace.mk' V p.2 (N p.1 i j p.2))
      (J ×ˢ e.baseSet) :=
    contMDiffOn_connection_family_apply F.smooth F.connection e.open_baseSet
      (E j) (E i) (hE j) (hE i)
  let W := deriv (fun s => N s i j x) t
  have hW : HasDerivAt (fun s => N s i j x) W t :=
    (family_tangent_time_derivative (F.metric 0) e.open_baseSet
      (fun s => N s i j) hN ht).1 x hx
  let cov := (EuclideanSpace.proj l).comp (e.continuousLinearMapAt ℝ x)
  have hcov (v : TangentSpace (𝓡 n) x) : cov v = theta l x v := (htheta v).symm
  have hd : HasDerivAt (fun s => Gamma s x i j l) (theta l x W) t := by
    simpa only [Function.comp_def, hcov, Gamma] using
      cov.hasFDerivAt.comp_hasDerivAt t hW
  have hmetric (u w : V) :
      G x u w = (F.metric t).inner x (e.symmL ℝ x u) (e.symmL ℝ x w) := by
    dsimp only [G]
    rw [inCoordinates_apply_eq₂ (F₁ := V) (F₂ := V) (F₃ := ℝ)
      (E₁ := TangentSpace (𝓡 n)) (E₂ := TangentSpace (𝓡 n))
      (E₃ := fun _ : M => ℝ) hx hx (by simp)]
    rw [← Trivialization.symmL_apply (R := ℝ) e hx u,
      ← Trivialization.symmL_apply (R := ℝ) e hx w]
    simp only [Bundle.Trivial.fiberBundle_trivializationAt',
      Bundle.Trivial.linearMapAt_trivialization, LinearMap.id_coe, id_eq]
  have hEvalue (v : Fin n) : E v x = e.symmL ℝ x (cb v) := by
    dsimp only [E]
    rw [e.localFrame_apply_of_mem_baseSet cb hx]
    simp only [Trivialization.basisAt, Module.Basis.map_apply,
      Trivialization.linearEquivAt_symm_apply]
    exact (Trivialization.symmL_apply (R := ℝ) e hx (cb v)).symm
  have hdual : G x (e.continuousLinearMapAt ℝ x W) =
      ∑ v : Fin n, (F.metric t).inner x W (E v x) • EuclideanSpace.proj v := by
    ext w
    rw [hmetric, e.symmL_continuousLinearMapAt hx]
    have hw : w = ∑ v : Fin n, w v • cb v := by
      simpa only [cb, OrthonormalBasis.coe_toBasis_repr_apply,
        EuclideanSpace.basisFun_repr] using (cb.sum_repr w).symm
    nth_rw 1 [hw]
    simp only [map_sum, map_smul, hEvalue, sum_apply, smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro v _
    change w v * _ = _ * w v
    ring
  have hGi : (G x).IsInvertible :=
    (contMDiffOn_family_metric_frame_inverse F.smooth x0).1 (t, x) hx
  have hreconstruct : theta l x W =
      ∑ v : Fin n, H x l v * (F.metric t).inner x W (E v x) := by
    rw [htheta]
    change EuclideanSpace.proj l (e.continuousLinearMapAt ℝ x W) = _
    rw [← hGi.inverse_apply_self (e.continuousLinearMapAt ℝ x W), hdual]
    simp only [map_sum, map_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro v _
    change (F.metric t).inner x W (E v x) * H x l v =
      H x l v * (F.metric t).inner x W (E v x)
    ring
  have hpair (v : Fin n) := ricciFlow_connection_variation_pairing_eq_inverse_frame
    F ht x0 (E i) (E j) (E v) (hE i) (hE j) (hE v) hx
  have hp (v : Fin n) : (F.metric t).inner x W (E v x) =
      -(∑ p : Fin n, ∑ q : Fin n, H x p q * L ![i,p,j,v,q] x) -
        (∑ p : Fin n, ∑ q : Fin n, H x p q * L ![j,p,v,i,q] x) +
        ∑ p : Fin n, ∑ q : Fin n, H x p q * L ![v,p,i,j,q] x := by
    convert hpair v using 1
    rfl
  rw [hreconstruct] at hd
  simpa only [hp] using hd

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem hasDerivAt_ricciFlow_metric_frame_coordinates
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    {J : Set ℝ} (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J)
    (x0 : M) :
    let V := EuclideanSpace ℝ (Fin n)
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let cb := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let E := e.localFrame cb
    let G := fun (s : ℝ) (x : M) (i j : Fin n) =>
      (F.metric s).inner x (E i x) (E j x)
    let A := fun x : M => ContinuousLinearMap.inCoordinates V
      (TangentSpace (𝓡 n)) (V →L[ℝ] ℝ)
      (fun y => TangentSpace (𝓡 n) y →L[ℝ] ℝ)
      x0 x x0 x ((F.metric t).inner x)
    let H := fun (x : M) (p q : Fin n) =>
      (A x).inverse (EuclideanSpace.proj q) p
    let L0 := fun (alpha : Fin 4 → Fin n) (x : M) =>
      (F.metric t).inner x
        (curvatureOnFields_iteratedCovariantDerivative (F.connection t) 0
          (fun j : Fin 3 => E (alpha j.castSucc)) x)
        (E (alpha (Fin.last 3)) x)
    ∀ x ∈ e.baseSet, ∀ i j : Fin n,
      HasDerivAt (fun s => G s x i j)
        (-2 * (∑ p : Fin n, ∑ q : Fin n,
          H x p q * L0 ![p,i,j,q] x)) t := by
  classical
  let g := F.metric t
  let D := F.connection t
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  dsimp only
  let V := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt V (TangentSpace (𝓡 n)) x0
  let cb := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let E := e.localFrame cb
  let theta := e.localFrameCoeff (𝓡 n) cb
  let G := fun (s : ℝ) (x : M) (i j : Fin n) =>
    (F.metric s).inner x (E i x) (E j x)
  let A := fun x : M => ContinuousLinearMap.inCoordinates V
    (TangentSpace (𝓡 n)) (V →L[ℝ] ℝ)
    (fun y => TangentSpace (𝓡 n) y →L[ℝ] ℝ) x0 x x0 x (g.inner x)
  let H := fun (x : M) (p q : Fin n) => (A x).inverse (EuclideanSpace.proj q) p
  let L0 := fun (alpha : Fin 4 → Fin n) (x : M) =>
    g.inner x (curvatureOnFields_iteratedCovariantDerivative D 0
      (fun j : Fin 3 => E (alpha j.castSucc)) x) (E (alpha (Fin.last 3)) x)
  intro x hx i j
  change HasDerivAt (fun s => G s x i j)
    (-2 * (∑ p : Fin n, ∑ q : Fin n, H x p q * L0 ![p,i,j,q] x)) t
  let b := g.orthonormalBasis x
  have hE (p : Fin n) : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% (E p)) e.baseSet :=
    e.contMDiffOn_localFrame_baseSet (I := 𝓡 n) ∞ cb p
  have hframe (W : TangentSpace (𝓡 n) x) :
      W = ∑ p : Fin n, theta p x W • E p x := by
    simpa only [FiberBundle.extend_apply_self] using
      e.eq_sum_localFrameCoeff_smul (I := 𝓡 n) (b := cb)
        (s := FiberBundle.extend V W) hx
  have hcoord (p : Fin n) (W : TangentSpace (𝓡 n) x) :
      theta p x W = (e.basisAt cb hx).repr W p := by
    simpa only [FiberBundle.extend_apply_self] using
      e.localFrameCoeff_apply_of_mem_baseSet (I := 𝓡 n) cb hx
        (FiberBundle.extend V W) p
  have hGram (p q : Fin n) :
      H x p q = ∑ r, theta p x (b r) * theta q x (b r) :=
    metric_inverse_eq_sum_orthonormal_coordinates g x0 x hx p q
  have hinner (W : TangentSpace (𝓡 n) x) (r) :
      (∑ q : Fin n, theta q x (b r) * g.inner x W (E q x)) = g.inner x W (b r) := by
    nth_rw 2 [hframe (b r)]
    simp only [map_sum, map_smul, smul_eq_mul]
  have horth (W : TangentSpace (𝓡 n) x) :
      (∑ r, g.inner x W (b r) • b r) = W := by
    have hh := b.sum_repr' W
    change (∑ r, g.inner x (b r) W • b r) = W at hh
    simpa only [g.symm x W] using hh
  have hcoeff (p : Fin n) (W : TangentSpace (𝓡 n) x) :
      (∑ q : Fin n, H x p q * g.inner x W (E q x)) = theta p x W := by
    simp only [hGram, Finset.sum_mul]
    rw [Finset.sum_comm]
    calc
      _ = ∑ r, theta p x (b r) *
          (∑ q : Fin n, theta q x (b r) * g.inner x W (E q x)) := by
        simp only [Finset.mul_sum, mul_assoc]
      _ = ∑ r, theta p x (b r) * g.inner x W (b r) := by simp only [hinner]
      _ = theta p x (∑ r, g.inner x W (b r) • b r) := by
        simp only [map_sum, map_smul, smul_eq_mul, mul_comm]
      _ = _ := by rw [horth]
  have htrace : D.ricci x (E i x) (E j x) =
      ∑ p : Fin n, ∑ q : Fin n, H x p q * L0 ![p,i,j,q] x := by
    calc
      _ = ∑ p : Fin n, theta p x (D.curvature x (E p x) (E i x) (E j x)) := by
        rw [ricci_eq_sum_basis_of_curvature_pairing D x (E i x) (E j x) (e.basisAt cb hx)]
        apply Finset.sum_congr rfl
        intro p _
        rw [hcoord]
        congr 2
        exact congrArg (fun W : TangentSpace (𝓡 n) x =>
          D.curvature x W (E i x) (E j x)) (e.localFrame_apply_of_mem_baseSet cb hx).symm
      _ = ∑ p : Fin n, ∑ q : Fin n, H x p q * L0 ![p,i,j,q] x := by
        apply Finset.sum_congr rfl
        intro p _
        rw [← hcoeff]
        apply Finset.sum_congr rfl
        intro q _
        congr 1
        rw [curvature_eq_curvatureOnFields D e.open_baseSet
          (E p) (E i) (E j) (hE p) (hE i) (hE j) hx]
        rfl
  have he := (F.equation t (interior_subset ht) x (E i x) (E j x)).hasDerivAt
    (mem_interior_iff_mem_nhds.mp ht)
  change HasDerivAt (fun s => G s x i j) (-2 * D.ricci x (E i x) (E j x)) t at he
  simpa only [htrace] using he

end PoincareConjecture.Proofs.M03
