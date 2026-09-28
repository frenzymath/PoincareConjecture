import PoincareConjecture.Proofs.M03.ConnectionVariation
import PoincareConjecture.Proofs.M03.RicciPairRegularity
import PoincareConjecture.Proofs.M03.ConnectionDifference
import PoincareConjecture.Proofs.M03.ConnectionRateEnergyAlgebra

set_option autoImplicit false
set_option maxHeartbeats 1800000

open scoped Manifold ContDiff Bundle Topology
open Set

universe u

namespace PoincareConjecture.Proofs.M03

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem ricciFlow_connection_difference_evolution_pairing
    {J J' : Set ℝ} (F : RicciFlow n M J) (F' : RicciFlow n M J')
    (hinit : F.metric 0 = F'.metric 0)
    {t : ℝ} (ht : t ∈ interior J) (ht' : t ∈ interior J')
    {U : Set M} (hU : IsOpen U)
    (X Y Z : (x : M) → TangentSpace (𝓡 n) x)
    (hX : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U)
    (hZ : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) U)
    {x : M} (hx : x ∈ U) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric 0).toRiemannianMetric⟩
    let c := extChartAt (𝓡 n) x
    let R := fun y (a b : TangentSpace (𝓡 n) y) =>
      (F.connection t).ricci y a b - (F'.connection t).ricci y a b
    let cR := fun (B C D : (y : M) → TangentSpace (𝓡 n) y) =>
      fderiv ℝ (fun z => R (c.symm z) (C (c.symm z)) (D (c.symm z)))
          (c x) (B x) -
        R x ((F.connection t).connection C x (B x)) (D x) -
        R x (C x) ((F.connection t).connection D x (B x))
    let A := fun s => CovariantDerivative.difference
      (F.connection s).connection (F'.connection s).connection x (Y x) (X x)
    let V' := fun s => (F'.connection s).connection Y x (X x)
    HasDerivAt A (deriv A t) t ∧
      (F.metric t).inner x (deriv A t) (Z x) =
        -cR X Y Z - cR Y Z X + cR Z X Y +
          2 * (F'.connection t).ricci x (A t) (Z x) -
          ((F.metric t).inner x (deriv V' t) (Z x) -
            (F'.metric t).inner x (deriv V' t) (Z x)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric 0).toRiemannianMetric⟩
  let c := extChartAt (𝓡 n) x
  let r := fun y (a b : TangentSpace (𝓡 n) y) => (F.connection t).ricci y a b
  let r' := fun y (a b : TangentSpace (𝓡 n) y) => (F'.connection t).ricci y a b
  let R := fun y (a b : TangentSpace (𝓡 n) y) => r y a b - r' y a b
  let D := fun (B C : (y : M) → TangentSpace (𝓡 n) y) =>
    (F.connection t).connection C x (B x)
  let D' := fun (B C : (y : M) → TangentSpace (𝓡 n) y) =>
    (F'.connection t).connection C x (B x)
  let Bdiff := fun (B C : (y : M) → TangentSpace (𝓡 n) y) => D B C - D' B C
  let C := fun (B C W : (y : M) → TangentSpace (𝓡 n) y) =>
    fderiv ℝ (fun z => r (c.symm z) (C (c.symm z)) (W (c.symm z))) (c x) (B x) -
      r x (D B C) (W x) - r x (C x) (D B W)
  let C' := fun (B C W : (y : M) → TangentSpace (𝓡 n) y) =>
    fderiv ℝ (fun z => r' (c.symm z) (C (c.symm z)) (W (c.symm z))) (c x) (B x) -
      r' x (D' B C) (W x) - r' x (C x) (D' B W)
  let cR := fun (B C W : (y : M) → TangentSpace (𝓡 n) y) =>
    fderiv ℝ (fun z => R (c.symm z) (C (c.symm z)) (W (c.symm z))) (c x) (B x) -
      R x (D B C) (W x) - R x (C x) (D B W)
  let A := fun s => CovariantDerivative.difference
    (F.connection s).connection (F'.connection s).connection x (Y x) (X x)
  let V := fun s => (F.connection s).connection Y x (X x)
  let V' := fun s => (F'.connection s).connection Y x (X x)
  change HasDerivAt A (deriv A t) t ∧
    (F.metric t).inner x (deriv A t) (Z x) =
      -cR X Y Z - cR Y Z X + cR Z X Y + 2 * r' x (A t) (Z x) -
        ((F.metric t).inner x (deriv V' t) (Z x) -
          (F'.metric t).inner x (deriv V' t) (Z x))
  have hXx := (hX.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hYx := (hY.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hZx := (hZ.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hAeq (s : ℝ) : A s = V s - V' s := by
    have hh := IsCovariantDerivativeOn.difference_apply
      (F.connection s).connection.isCovariantDerivativeOnUniv
      (F'.connection s).connection.isCovariantDerivativeOnUniv (mem_univ x) hYx
    have hh' := congrArg
      (fun L : TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x => L (X x)) hh
    dsimp only [A, V, V']
    exact hh'
  have hv : HasDerivAt V (deriv V t) t ∧
      (F.metric t).inner x (deriv V t) (Z x) = -C X Y Z - C Y Z X + C Z X Y :=
    ricciFlow_connection_variation_pairing F ht hU X Y Z hX hY hZ hx
  have hv' : HasDerivAt V' (deriv V' t) t ∧
      (F'.metric t).inner x (deriv V' t) (Z x) = -C' X Y Z - C' Y Z X + C' Z X Y := by
    simpa only [← hinit] using
      (ricciFlow_connection_variation_pairing F' ht' hU X Y Z hX hY hZ hx)
  have hAd := (hv.1.sub hv'.1).congr_of_eventuallyEq (Filter.Eventually.of_forall hAeq)
  have hAdot : deriv A t = deriv V t - deriv V' t := hAd.deriv
  refine ⟨hAd.differentiableAt.hasDerivAt, ?_⟩
  have hcx : c.symm (c x) = x := c.left_inv (mem_extChartAt_source x)
  have hcxt : c x ∈ c.target := mem_extChartAt_target x
  have hcxU : c.symm (c x) ∈ U := by simpa only [hcx] using hx
  have hc : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) ∞ c.symm (c x) :=
    (contMDiffOn_extChartAt_symm (I := 𝓡 n) x).contMDiffAt
      (extChartAt_target_mem_nhds' hcxt)
  have hspace {K : Set ℝ} (H : RicciFlow n M K) (htK : t ∈ interior K)
      (B W : (y : M) → TangentSpace (𝓡 n) y)
      (hB : ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% B) U)
      (hW : ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% W) U) :
      DifferentiableAt ℝ (fun z => (H.connection t).ricci (c.symm z)
        (B (c.symm z)) (W (c.symm z))) (c x) := by
    have hn : interior K ×ˢ (c.target ∩ c.symm ⁻¹' U) ∈ 𝓝 (t, c x) :=
      prod_mem_nhds (isOpen_interior.mem_nhds htK)
        (Filter.inter_mem (extChartAt_target_mem_nhds' hcxt)
          (hc.continuousAt.preimage_mem_nhds (hU.mem_nhds hcxU)))
    have hh := (contDiffOn_ricciFlow_ricci_chart_pair H hU B W hB hW x).contDiffAt hn
    have hs := hh.comp (c x) (contDiffAt_const.prodMk contDiffAt_id)
    exact hs.differentiableAt (by simp)
  have hds (B W : (y : M) → TangentSpace (𝓡 n) y)
      (hB : ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% B) U)
      (hW : ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% W) U)
      (a : EuclideanSpace ℝ (Fin n)) :
      fderiv ℝ (fun z => R (c.symm z) (B (c.symm z)) (W (c.symm z))) (c x) a =
      fderiv ℝ (fun z => r (c.symm z) (B (c.symm z)) (W (c.symm z))) (c x) a -
          fderiv ℝ (fun z => r' (c.symm z) (B (c.symm z)) (W (c.symm z))) (c x) a := by
    have hh := fderiv_sub (hspace F ht B W hB hW) (hspace F' ht' B W hB hW)
    change fderiv ℝ
        ((fun z => r (c.symm z) (B (c.symm z)) (W (c.symm z))) -
          (fun z => r' (c.symm z) (B (c.symm z)) (W (c.symm z)))) (c x) a = _
    simpa only [sub_apply] using congrArg
      (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => L a) hh
  have he (a b : TangentSpace (𝓡 n) x) :
      HasDerivAt (fun s => (F'.metric s).inner x a b) (-2 * r' x a b) t :=
    (F'.equation t (interior_subset ht') x a b).hasDerivAt
      (mem_interior_iff_mem_nhds.mp ht')
  have hsub₁ (a b z : TangentSpace (𝓡 n) x) :
      r' x (a - b) z = r' x a z - r' x b z := by
    have hd : HasDerivAt (fun s => (F'.metric s).inner x (a - b) z)
        (-2 * r' x a z - (-2 * r' x b z)) t := by
      refine ((he a z).sub (he b z)).congr_of_eventuallyEq ?_
      exact Filter.Eventually.of_forall (fun s => by
        simp only [Pi.sub_apply, map_sub, sub_apply])
    have hh := (he (a - b) z).unique hd
    linarith only [hh]
  have hsub₂ (a b z : TangentSpace (𝓡 n) x) :
      r' x a (b - z) = r' x a b - r' x a z := by
    have hd : HasDerivAt (fun s => (F'.metric s).inner x a (b - z))
        (-2 * r' x a b - (-2 * r' x a z)) t := by
      refine ((he a b).sub (he a z)).congr_of_eventuallyEq ?_
      exact Filter.Eventually.of_forall (fun s => by
        simp only [Pi.sub_apply, map_sub, sub_apply])
    have hh := (he a (b - z)).unique hd
    linarith only [hh]
  have hsymm (a b : TangentSpace (𝓡 n) x) : r' x a b = r' x b a := by
    have hb := (he b a).congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun s => (F'.metric s).symm x a b))
    have hh := (he a b).unique hb
    linarith only [hh]
  have hCs (B W Q : (y : M) → TangentSpace (𝓡 n) y)
      (hW : ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% W) U)
      (hQ : ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Q) U) :
      C B W Q - C' B W Q =
        cR B W Q - r' x (Bdiff B W) (Q x) - r' x (W x) (Bdiff B Q) := by
    dsimp only [C, C', cR]
    rw [hds W Q hW hQ (B x)]
    dsimp only [R, Bdiff]
    rw [hsub₁, hsub₂]
    ring
  have hBsymm (B W : (y : M) → TangentSpace (𝓡 n) y)
      (hB : MDifferentiableAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% B) x)
      (hW : MDifferentiableAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% W) x) :
      Bdiff B W = Bdiff W B := by
    have hh : D B W - D W B = VectorField.mlieBracket (𝓡 n) B W x :=
      ((F.connection t).connection.torsion_eq_zero_iff.mp
        (F.connection t).torsion_eq_zero) hB hW
    have hh' : D' B W - D' W B = VectorField.mlieBracket (𝓡 n) B W x :=
      ((F'.connection t).connection.torsion_eq_zero_iff.mp
        (F'.connection t).torsion_eq_zero) hB hW
    rw [sub_eq_iff_eq_add] at hh hh'
    dsimp only [Bdiff]
    rw [hh, hh']
    module
  have h1 := hCs X Y Z hY hZ
  have h2 := hCs Y Z X hZ hX
  have h3 := hCs Z X Y hX hY
  rw [hBsymm Y X hYx hXx, hsymm (Z x) (Bdiff X Y),
    hsymm (Bdiff Y Z) (X x)] at h2
  rw [hBsymm Z X hZx hXx, hBsymm Z Y hZx hYx,
    hsymm (Bdiff X Z) (Y x)] at h3
  have hAt : A t = Bdiff X Y := hAeq t
  rw [hAdot, map_sub, sub_apply, hAt]
  linarith only [hv.2, hv'.2, h1, h2, h3]

section TerminalCoordinates

open scoped BigOperators
open Bundle Manifold Filter

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem ricciFlow_connection_coordinate_jets_terminal_control
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {T C a : ℝ} (hT : 0 < T) (F : RicciFlow n M (Ico 0 T))
    (hRm : ∀ s ∈ Ico 0 T, ∀ x : M,
      (F.connection s).curvatureTensorNorm x ≤ C)
    (ha : 0 < a) (haT : a < T) (x0 : M)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (hKchart : K ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) x0).target) :
    let V := EuclideanSpace ℝ (Fin n)
    let c := chartAt V x0
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let cb := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let E := e.localFrame cb
    let theta := e.localFrameCoeff (𝓡 n) cb
    let Gamma := fun (s : ℝ) (i j l : Fin n) (z : V) =>
      theta l (c.symm z)
        ((F.connection s).connection (E j) (c.symm z) (E i (c.symm z)))
    ∀ m : ℕ, ∃ B R : ℝ, 0 ≤ B ∧ 0 ≤ R ∧
      (∀ q ≤ m, ∀ s ∈ Ico a T, ∀ z ∈ K, ∀ i j l : Fin n,
        ‖iteratedFDeriv ℝ q (Gamma s i j l) z‖ ≤ B) ∧
      (∀ q ≤ m, ∀ s ∈ Ico a T, ∀ z ∈ K, ∀ i j l : Fin n,
        DifferentiableAt ℝ
            (fun r => iteratedFDeriv ℝ q (Gamma r i j l) z) s ∧
          ‖deriv (fun r => iteratedFDeriv ℝ q (Gamma r i j l) z) s‖ ≤ R) ∧
      (∀ q ≤ m, ∀ s ∈ Ico a T, ∀ t ∈ Ico a T,
        ∀ z ∈ K, ∀ i j l : Fin n,
          ‖iteratedFDeriv ℝ q (Gamma t i j l) z -
              iteratedFDeriv ℝ q (Gamma s i j l) z‖ ≤ R * |t - s|) := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric 0).toRiemannianMetric⟩
  let V := EuclideanSpace ℝ (Fin n)
  let c := chartAt V x0
  let e := trivializationAt V (TangentSpace (𝓡 n)) x0
  let cb := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let E := e.localFrame cb
  let theta := e.localFrameCoeff (𝓡 n) cb
  let N := fun (s : ℝ) (i j : Fin n) (x : M) =>
    (F.connection s).connection (E j) x (E i x)
  let Gamma := fun (s : ℝ) (i j l : Fin n) (z : V) =>
    theta l (c.symm z) (N s i j (c.symm z))
  let G := fun (s : ℝ) (x : M) => ContinuousLinearMap.inCoordinates V
    (TangentSpace (𝓡 n)) (V →L[ℝ] ℝ)
    (fun y => TangentSpace (𝓡 n) y →L[ℝ] ℝ)
    x0 x x0 x ((F.metric s).inner x)
  let H := fun (s : ℝ) (i j : Fin n) (z : V) =>
    (G s (c.symm z)).inverse (EuclideanSpace.proj j) i
  let L := fun (r : ℕ) (s : ℝ) (alpha : Fin (r + 4) → Fin n) (z : V) =>
    (F.metric s).inner (c.symm z)
      (curvatureOnFields_iteratedCovariantDerivative (F.connection s) r
        (fun j : Fin (r + 3) => E (alpha j.castSucc)) (c.symm z))
      (E (alpha (Fin.last (r + 3))) (c.symm z))
  let tr := fun (s : ℝ) (i j k : Fin n) (z : V) =>
    ∑ p : Fin n, ∑ q : Fin n, H s p q z * L 1 s ![i,p,j,k,q] z
  let b := fun (s : ℝ) (i j v : Fin n) (z : V) =>
    -tr s i j v z - tr s j v i z + tr s v i j z
  let Q := fun (s : ℝ) (i j l : Fin n) (z : V) =>
    ∑ v : Fin n, H s l v z * b s i j v z
  let Good := fun m : ℕ => ∃ B R : ℝ, 0 ≤ B ∧ 0 ≤ R ∧
    (∀ q ≤ m, ∀ s ∈ Ico a T, ∀ z ∈ K, ∀ i j l : Fin n,
      ‖iteratedFDeriv ℝ q (Gamma s i j l) z‖ ≤ B) ∧
    (∀ q ≤ m, ∀ s ∈ Ico a T, ∀ z ∈ K, ∀ i j l : Fin n,
      DifferentiableAt ℝ
          (fun r => iteratedFDeriv ℝ q (Gamma r i j l) z) s ∧
        ‖deriv (fun r => iteratedFDeriv ℝ q (Gamma r i j l) z) s‖ ≤ R) ∧
    (∀ q ≤ m, ∀ s ∈ Ico a T, ∀ t ∈ Ico a T,
      ∀ z ∈ K, ∀ i j l : Fin n,
        ‖iteratedFDeriv ℝ q (Gamma t i j l) z -
            iteratedFDeriv ℝ q (Gamma s i j l) z‖ ≤ R * |t - s|)
  change ∀ m : ℕ, Good m
  have hbase {z : V} (hz : z ∈ c.target) : c.symm z ∈ e.baseSet := by
    simpa only [e, TangentBundle.trivializationAt_baseSet] using c.map_target hz
  have haI : a ∈ Ico a T := ⟨le_rfl, haT⟩
  have htime {s : ℝ} (hs : s ∈ Ico a T) : s ∈ Ioo 0 T :=
    ⟨ha.trans_le hs.1, hs.2⟩
  have hE (i : Fin n) : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% (E i)) e.baseSet :=
    e.contMDiffOn_localFrame_baseSet (I := 𝓡 n) ∞ cb i
  have htheta {x : M} (hx : x ∈ e.baseSet) (l : Fin n)
      (v : TangentSpace (𝓡 n) x) :
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
  have hchart (f : M → ℝ)
      (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f e.baseSet) :
      ContDiffOn ℝ ∞ (fun z => f (c.symm z)) c.target :=
    (hf.comp (contMDiffOn_chart_symm (I := 𝓡 n) (n := ∞) (x := x0))
      (fun z hz => hbase hz)).contDiffOn
  have hGammaSmooth (s : ℝ) (i j l : Fin n) :
      ContDiffOn ℝ ∞ (Gamma s i j l) c.target := by
    apply hchart (fun y => theta l y (N s i j y))
    exact contMDiffOn_localFrameCoeff cb e.open_baseSet subset_rfl
      ((F.connection s).contMDiffOn_connection_apply e.open_baseSet
        (E i) (E j) (hE i) (hE j)) l
  have hGammaJoint (i j l : Fin n) : ContDiffOn ℝ ∞
      (Function.uncurry (fun s => Gamma s i j l)) (Ioo 0 T ×ˢ c.target) := by
    have hN : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n))
        ((𝓡 n).prod 𝓘(ℝ, V)) ∞
        (fun p : ℝ × M => TotalSpace.mk' V p.2 (N p.1 i j p.2))
        (Ico 0 T ×ˢ e.baseSet) :=
      contMDiffOn_connection_family_apply F.smooth F.connection e.open_baseSet
        (E j) (E i) (hE j) (hE i)
    have hcoords := (e.contMDiffOn_iff (by
      intro p hp
      change p.2 ∈ e.baseSet
      exact hp.2)).mp hN
    have hg : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => theta l p.2 (N p.1 i j p.2))
        (Ico 0 T ×ˢ e.baseSet) := by
      apply ((EuclideanSpace.proj l : V →L[ℝ] ℝ).contMDiff.comp_contMDiffOn
        hcoords.2).congr
      intro p hp
      rw [htheta hp.2, Trivialization.continuousLinearMapAt_apply_of_mem ℝ e hp.2]
      rfl
    have hmap : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, V))
        (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
        (fun p : ℝ × V => (p.1, c.symm p.2)) (Ioo 0 T ×ˢ c.target) :=
      contMDiffOn_fst.prodMk
        ((contMDiffOn_chart_symm (I := 𝓡 n) (n := ∞) (x := x0)).comp
          contMDiffOn_snd (fun p hp => hp.2))
    have hh := hg.comp hmap (fun p hp => ⟨⟨hp.1.1.le, hp.1.2⟩, hbase hp.2⟩)
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hh
    exact hh.contDiffOn
  have hfamily (s : ℝ) : RiemannianMetric.IsSmoothFamilyOn
      (fun _ : ℝ => F.metric s) Set.univ :=
    ((F.metric s).contMDiff.comp contMDiff_snd).contMDiffOn
  have hHSmooth (s : ℝ) (i j : Fin n) :
      ContDiffOn ℝ ∞ (H s i j) c.target := by
    have hInv : ContMDiffOn (𝓡 n) 𝓘(ℝ, (V →L[ℝ] ℝ) →L[ℝ] V) ∞
        (fun y => (G s y).inverse) e.baseSet :=
      (contMDiffOn_family_metric_frame_inverse (hfamily s) x0).2.2.comp
        (show ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
          (fun y : M => ((0 : ℝ), y)) e.baseSet from
          contMDiffOn_const.prodMk contMDiffOn_id)
        (fun y hy => ⟨Set.mem_univ (0 : ℝ), hy⟩)
    apply hchart (fun y => (EuclideanSpace.proj i : V →L[ℝ] ℝ)
      ((G s y).inverse (EuclideanSpace.proj j)))
    exact (EuclideanSpace.proj i : V →L[ℝ] ℝ).contMDiff.comp_contMDiffOn
      (hInv.clm_apply (contMDiffOn_const (c := EuclideanSpace.proj j)))
  have hLSmooth (s : ℝ) (alpha : Fin 5 → Fin n) :
      ContDiffOn ℝ ∞ (L 1 s alpha) c.target := by
    apply hchart (fun y => (F.metric s).inner y
      (curvatureOnFields_iteratedCovariantDerivative (F.connection s) 1
        (fun j : Fin 4 => E (alpha j.castSucc)) y)
      (E (alpha (Fin.last 4)) y))
    exact (contMDiffOn_family_metric_pair (hfamily s)
      (curvatureOnFields_iteratedCovariantDerivative (F.connection s) 1
        (fun j : Fin 4 => E (alpha j.castSucc)))
      (E (alpha (Fin.last 4)))
      (contMDiffOn_curvatureOnFields_iteratedCovariantDerivative (F.connection s)
        e.open_baseSet 1 _ (fun j => hE (alpha j.castSucc)))
      (hE (alpha (Fin.last 4)))).comp
      (show ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
        (fun y : M => ((0 : ℝ), y)) e.baseSet from
        contMDiffOn_const.prodMk contMDiffOn_id)
      (fun y hy => ⟨Set.mem_univ (0 : ℝ), hy⟩)
  have htrSmooth (s : ℝ) (i j k : Fin n) : ContDiffOn ℝ ∞ (tr s i j k) c.target :=
    ContDiffOn.sum (fun p _ => ContDiffOn.sum (fun q _ =>
      (hHSmooth s p q).mul (hLSmooth s ![i,p,j,k,q])))
  have hbSmooth (s : ℝ) (i j v : Fin n) : ContDiffOn ℝ ∞ (b s i j v) c.target :=
    ((htrSmooth s i j v).neg.sub (htrSmooth s j v i)).add (htrSmooth s v i j)
  have hGtime {s : ℝ} (hs : s ∈ Ioo 0 T) {z : V} (hz : z ∈ c.target)
      (i j l : Fin n) : HasDerivAt (fun r => Gamma r i j l z) (Q s i j l z) s :=
    hasDerivAt_ricciFlow_connection_frame_coordinates F
      (by simpa only [interior_Ico] using hs) x0 (c.symm z) (hbase hz) i j l
  have hjetTime (q : ℕ) {s : ℝ} (hs : s ∈ Ioo 0 T) {z : V} (hz : z ∈ c.target)
      (i j l : Fin n) :
      HasDerivAt (fun r => iteratedFDeriv ℝ q (Gamma r i j l) z)
        (iteratedFDeriv ℝ q (Q s i j l) z) s := by
    have hh := hasDerivAt_iteratedFDeriv_family isOpen_Ioo c.open_target
      (fun r => Gamma r i j l) (hGammaJoint i j l) q hs hz
    have he : (fun y => deriv (fun r => Gamma r i j l y) s) =ᶠ[𝓝 z] Q s i j l := by
      filter_upwards [c.open_target.mem_nhds hz] with y hy
      exact (hGtime hs hy i j l).deriv
    exact hh.congr_deriv (he.iteratedFDeriv (𝕜 := ℝ) q).eq_of_nhds
  have hsum {d : ℕ} (f : Fin d → V → ℝ)
      (hf : ∀ i, ContDiffOn ℝ ∞ (f i) c.target)
      (z : V) (hz : z ∈ c.target) (q : ℕ) (B : ℝ)
      (hb : ∀ i, ‖iteratedFDeriv ℝ q (f i) z‖ ≤ B) :
      ‖iteratedFDeriv ℝ q (fun y => ∑ i, f i y) z‖ ≤ (d : ℝ) * B := by
    rw [iteratedFDeriv_fun_sum_apply
      (fun i _ => ((hf i).contDiffAt (c.open_target.mem_nhds hz)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl q))]
    calc
      _ ≤ ∑ i : Fin d, ‖iteratedFDeriv ℝ q (f i) z‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin d, B := Finset.sum_le_sum (fun i _ => hb i)
      _ = (d : ℝ) * B := by simp
  have hstep (m : ℕ)
      (hprev : ∃ A : ℝ, 0 ≤ A ∧
        ∀ q < m, ∀ s ∈ Ico a T, ∀ z ∈ K, ∀ i j l : Fin n,
          ‖iteratedFDeriv ℝ q (Gamma s i j l) z‖ ≤ A) : Good m := by
    obtain ⟨⟨BH, hBH, hHbound⟩, hLbound⟩ :=
      ricciFlow_inverse_and_lowered_coordinate_jets_of_connection_jets
        hT F hRm ha haT x0 hK hKchart m hprev
    obtain ⟨BL, hBL, hL1bound⟩ := hLbound 1
    let P := (2 : ℝ) ^ m * BH * BL
    let S := (n : ℝ) * ((n : ℝ) * P)
    let Btr := S + S + S
    let R := (n : ℝ) * ((2 : ℝ) ^ m * BH * Btr)
    have hP : 0 ≤ P := by dsimp only [P]; positivity
    have hS : 0 ≤ S := by dsimp only [S]; positivity
    have hBtr : 0 ≤ Btr := by dsimp only [Btr]; positivity
    have hR : 0 ≤ R := by dsimp only [R]; positivity
    have hmulBound (q : ℕ) (hq : q ≤ m) {s : ℝ} (hs : s ∈ Ico a T)
        {z : V} (hz : z ∈ K) (p v : Fin n) (alpha : Fin 5 → Fin n) :
        ‖iteratedFDeriv ℝ q (fun y => H s p v y * L 1 s alpha y) z‖ ≤ P := by
      apply (norm_iteratedFDeriv_mul_le_of_open_bounds c.open_target
        (hHSmooth s p v) (hLSmooth s alpha) (hKchart hz) q hBH hBL
        (fun k hk => hHbound k (hk.trans hq) s hs z hz p v)
        (fun k hk => hL1bound k (hk.trans hq) s hs z hz alpha)).trans
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hq) hBH) hBL
    have htrBound (q : ℕ) (hq : q ≤ m) {s : ℝ} (hs : s ∈ Ico a T)
        {z : V} (hz : z ∈ K) (i j k : Fin n) :
        ‖iteratedFDeriv ℝ q (tr s i j k) z‖ ≤ S := by
      apply hsum _ (fun p => ContDiffOn.sum (fun v _ =>
        (hHSmooth s p v).mul (hLSmooth s ![i,p,j,k,v]))) z (hKchart hz) q ((n : ℝ) * P)
      intro p
      apply hsum _ (fun v => (hHSmooth s p v).mul (hLSmooth s ![i,p,j,k,v]))
        z (hKchart hz) q P
      intro v
      exact hmulBound q hq hs hz p v ![i,p,j,k,v]
    have hbBound (q : ℕ) (hq : q ≤ m) {s : ℝ} (hs : s ∈ Ico a T)
        {z : V} (hz : z ∈ K) (i j v : Fin n) :
        ‖iteratedFDeriv ℝ q (b s i j v) z‖ ≤ Btr := by
      have hc (i j k : Fin n) : ContDiffAt ℝ q (tr s i j k) z :=
        ((htrSmooth s i j k).contDiffAt (c.open_target.mem_nhds (hKchart hz))).of_le
          (ENat.natCast_le_of_coe_top_le_withTop le_rfl q)
      have hneg : iteratedFDeriv ℝ q (fun y => -tr s i j v y) z =
          -iteratedFDeriv ℝ q (tr s i j v) z := by
        simpa only [Pi.neg_def] using
          (iteratedFDeriv_neg_apply (𝕜 := ℝ) (i := q) (f := tr s i j v) (x := z))
      dsimp only [b]
      rw [fun_iteratedFDeriv_add_apply ((hc i j v).neg.sub (hc j v i)) (hc v i j),
        fun_iteratedFDeriv_sub_apply (hc i j v).neg (hc j v i),
        hneg]
      calc
        _ ≤ ‖-iteratedFDeriv ℝ q (tr s i j v) z - iteratedFDeriv ℝ q (tr s j v i) z‖ +
            ‖iteratedFDeriv ℝ q (tr s v i j) z‖ := norm_add_le _ _
        _ ≤ (‖iteratedFDeriv ℝ q (tr s i j v) z‖ +
            ‖iteratedFDeriv ℝ q (tr s j v i) z‖) +
            ‖iteratedFDeriv ℝ q (tr s v i j) z‖ :=
          add_le_add (by
            simpa only [norm_neg] using (norm_sub_le
              (-iteratedFDeriv ℝ q (tr s i j v) z)
              (iteratedFDeriv ℝ q (tr s j v i) z))) le_rfl
        _ ≤ Btr := add_le_add (add_le_add (htrBound q hq hs hz i j v)
          (htrBound q hq hs hz j v i)) (htrBound q hq hs hz v i j)
    have hQbound (q : ℕ) (hq : q ≤ m) {s : ℝ} (hs : s ∈ Ico a T)
        {z : V} (hz : z ∈ K) (i j l : Fin n) :
        ‖iteratedFDeriv ℝ q (Q s i j l) z‖ ≤ R := by
      apply hsum _ (fun v => (hHSmooth s l v).mul (hbSmooth s i j v))
        z (hKchart hz) q ((2 : ℝ) ^ m * BH * Btr)
      intro v
      apply (norm_iteratedFDeriv_mul_le_of_open_bounds c.open_target
        (hHSmooth s l v) (hbSmooth s i j v) (hKchart hz) q hBH hBtr
        (fun k hk => hHbound k (hk.trans hq) s hs z hz l v)
        (fun k hk => hbBound k (hk.trans hq) hs hz i j v)).trans
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hq) hBH) hBtr
    have hinitial (q : Fin (m + 1)) (i j l : Fin n) :
        ∃ B0 : ℝ, 0 ≤ B0 ∧ ∀ z ∈ K,
          ‖iteratedFDeriv ℝ (q : ℕ) (Gamma a i j l) z‖ ≤ B0 := by
      have hc := ContinuousOn.continuousOn_iteratedFDeriv
        (hGammaSmooth a i j l) c.open_target
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl (q : ℕ))
      obtain ⟨B0, hB0⟩ := hK.bddAbove_image (hc.norm.mono hKchart)
      refine ⟨max B0 0, le_max_right _ _, ?_⟩
      intro z hz
      exact (hB0 (mem_image_of_mem _ hz)).trans (le_max_left _ _)
    choose b0 hb0 hbound0 using hinitial
    let B0 := ∑ q : Fin (m + 1), ∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin n, b0 q i j l
    have hB0 : 0 ≤ B0 := Finset.sum_nonneg fun q _ => Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun l _ => hb0 q i j l
    have hB0bound (q : Fin (m + 1)) (i j l : Fin n) : b0 q i j l ≤ B0 := by
      calc
        _ ≤ ∑ l : Fin n, b0 q i j l :=
          Finset.single_le_sum (fun l _ => hb0 q i j l) (Finset.mem_univ l)
        _ ≤ ∑ j : Fin n, ∑ l : Fin n, b0 q i j l := Finset.single_le_sum
          (fun j _ => Finset.sum_nonneg fun l _ => hb0 q i j l) (Finset.mem_univ j)
        _ ≤ ∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin n, b0 q i j l := Finset.single_le_sum
          (fun i _ => Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun l _ => hb0 q i j l)
          (Finset.mem_univ i)
        _ ≤ B0 := Finset.single_le_sum
          (fun q _ => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
            Finset.sum_nonneg fun l _ => hb0 q i j l) (Finset.mem_univ q)
    have hlip (q : ℕ) (hq : q ≤ m) {s t : ℝ} (hs : s ∈ Ico a T) (ht : t ∈ Ico a T)
        {z : V} (hz : z ∈ K) (i j l : Fin n) :
        ‖iteratedFDeriv ℝ q (Gamma t i j l) z -
            iteratedFDeriv ℝ q (Gamma s i j l) z‖ ≤ R * |t - s| := by
      have hh := (convex_Ico a T).norm_image_sub_le_of_norm_hasDerivWithin_le
        (f := fun r => iteratedFDeriv ℝ q (Gamma r i j l) z)
        (f' := fun r => iteratedFDeriv ℝ q (Q r i j l) z)
        (fun r hr => (hjetTime q (htime hr) (hKchart hz) i j l).hasDerivWithinAt)
        (fun r hr => hQbound q hq hr hz i j l) hs ht
      simpa only [Real.norm_eq_abs] using hh
    refine ⟨B0 + R * (T - a), R, add_nonneg hB0 (mul_nonneg hR (sub_nonneg.mpr haT.le)),
      hR, ?_, ?_, ?_⟩
    · intro q hq s hs z hz i j l
      let qf : Fin (m + 1) := ⟨q, Nat.lt_succ_of_le hq⟩
      have hstart := (hbound0 qf i j l z hz).trans (hB0bound qf i j l)
      have hd := hlip q hq haI hs hz i j l
      rw [abs_of_nonneg (sub_nonneg.mpr hs.1)] at hd
      calc
        ‖iteratedFDeriv ℝ q (Gamma s i j l) z‖ =
            ‖iteratedFDeriv ℝ q (Gamma a i j l) z +
              (iteratedFDeriv ℝ q (Gamma s i j l) z -
                iteratedFDeriv ℝ q (Gamma a i j l) z)‖ := by congr 1; abel
        _ ≤ ‖iteratedFDeriv ℝ q (Gamma a i j l) z‖ +
            ‖iteratedFDeriv ℝ q (Gamma s i j l) z -
              iteratedFDeriv ℝ q (Gamma a i j l) z‖ := norm_add_le _ _
        _ ≤ B0 + R * (s - a) := add_le_add hstart hd
        _ ≤ B0 + R * (T - a) := add_le_add le_rfl
          (mul_le_mul_of_nonneg_left (sub_le_sub_right hs.2.le a) hR)
    · intro q hq s hs z hz i j l
      have hd := hjetTime q (htime hs) (hKchart hz) i j l
      refine ⟨hd.differentiableAt, ?_⟩
      rw [hd.deriv]
      exact hQbound q hq hs hz i j l
    · intro q hq s hs t ht z hz i j l
      exact hlip q hq hs ht hz i j l
  intro m
  induction m with
  | zero =>
    apply hstep 0
    refine ⟨0, le_rfl, ?_⟩
    intro q hq
    exact (Nat.not_lt_zero q hq).elim
  | succ m ih =>
    obtain ⟨B, R, hB, hR, hb, hr, hlip⟩ := ih
    apply hstep (m + 1)
    refine ⟨B, hB, ?_⟩
    intro q hq s hs z hz i j l
    exact hb q (Nat.le_of_lt_succ hq) s hs z hz i j l

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem ricciFlow_metric_coordinate_jets_terminal_control
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {T C a : ℝ} (hT : 0 < T) (F : RicciFlow n M (Ico 0 T))
    (hRm : ∀ s ∈ Ico 0 T, ∀ x : M,
      (F.connection s).curvatureTensorNorm x ≤ C)
    (ha : 0 < a) (haT : a < T) (x0 : M)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (hKchart : K ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) x0).target) :
    let V := EuclideanSpace ℝ (Fin n)
    let c := chartAt V x0
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let E := e.localFrame (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let G := fun (s : ℝ) (i j : Fin n) (z : V) =>
      (F.metric s).inner (c.symm z) (E i (c.symm z)) (E j (c.symm z))
    ∀ m : ℕ, ∃ B R : ℝ, 0 ≤ B ∧ 0 ≤ R ∧
      (∀ q ≤ m, ∀ s ∈ Ico a T, ∀ z ∈ K, ∀ i j : Fin n,
        ‖iteratedFDeriv ℝ q (G s i j) z‖ ≤ B) ∧
      (∀ q ≤ m, ∀ s ∈ Ico a T, ∀ z ∈ K, ∀ i j : Fin n,
        DifferentiableAt ℝ
            (fun r => iteratedFDeriv ℝ q (G r i j) z) s ∧
          ‖deriv (fun r => iteratedFDeriv ℝ q (G r i j) z) s‖ ≤ R) ∧
      (∀ q ≤ m, ∀ s ∈ Ico a T, ∀ t ∈ Ico a T,
        ∀ z ∈ K, ∀ i j : Fin n,
          ‖iteratedFDeriv ℝ q (G t i j) z -
              iteratedFDeriv ℝ q (G s i j) z‖ ≤ R * |t - s|) := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric 0).toRiemannianMetric⟩
  let V := EuclideanSpace ℝ (Fin n)
  let c := chartAt V x0
  let e := trivializationAt V (TangentSpace (𝓡 n)) x0
  let cb := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let E := e.localFrame cb
  let G := fun (s : ℝ) (i j : Fin n) (z : V) =>
    (F.metric s).inner (c.symm z) (E i (c.symm z)) (E j (c.symm z))
  let A := fun (s : ℝ) (x : M) => ContinuousLinearMap.inCoordinates V
    (TangentSpace (𝓡 n)) (V →L[ℝ] ℝ)
    (fun y => TangentSpace (𝓡 n) y →L[ℝ] ℝ)
    x0 x x0 x ((F.metric s).inner x)
  let H := fun (s : ℝ) (i j : Fin n) (z : V) =>
    (A s (c.symm z)).inverse (EuclideanSpace.proj j) i
  let L := fun (r : ℕ) (s : ℝ) (alpha : Fin (r + 4) → Fin n) (z : V) =>
    (F.metric s).inner (c.symm z)
      (curvatureOnFields_iteratedCovariantDerivative (F.connection s) r
        (fun j : Fin (r + 3) => E (alpha j.castSucc)) (c.symm z))
      (E (alpha (Fin.last (r + 3))) (c.symm z))
  let tr := fun (s : ℝ) (i j : Fin n) (z : V) =>
    ∑ p : Fin n, ∑ q : Fin n, H s p q z * L 0 s ![p,i,j,q] z
  let Q := fun (s : ℝ) (i j : Fin n) (z : V) => -2 * tr s i j z
  change ∀ m : ℕ, ∃ B R : ℝ, 0 ≤ B ∧ 0 ≤ R ∧
    (∀ q ≤ m, ∀ s ∈ Ico a T, ∀ z ∈ K, ∀ i j : Fin n,
      ‖iteratedFDeriv ℝ q (G s i j) z‖ ≤ B) ∧
    (∀ q ≤ m, ∀ s ∈ Ico a T, ∀ z ∈ K, ∀ i j : Fin n,
      DifferentiableAt ℝ (fun r => iteratedFDeriv ℝ q (G r i j) z) s ∧
        ‖deriv (fun r => iteratedFDeriv ℝ q (G r i j) z) s‖ ≤ R) ∧
    (∀ q ≤ m, ∀ s ∈ Ico a T, ∀ t ∈ Ico a T, ∀ z ∈ K, ∀ i j : Fin n,
      ‖iteratedFDeriv ℝ q (G t i j) z - iteratedFDeriv ℝ q (G s i j) z‖ ≤ R * |t - s|)
  have hbase {z : V} (hz : z ∈ c.target) : c.symm z ∈ e.baseSet := by
    simpa only [e, TangentBundle.trivializationAt_baseSet] using c.map_target hz
  have htime {s : ℝ} (hs : s ∈ Ico a T) : s ∈ Ioo 0 T :=
    ⟨ha.trans_le hs.1, hs.2⟩
  have haI : a ∈ Ico a T := ⟨le_rfl, haT⟩
  have hE (i : Fin n) : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% (E i)) e.baseSet :=
    e.contMDiffOn_localFrame_baseSet (I := 𝓡 n) ∞ cb i
  have hchart (f : M → ℝ)
      (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f e.baseSet) :
      ContDiffOn ℝ ∞ (fun z => f (c.symm z)) c.target :=
    (hf.comp (contMDiffOn_chart_symm (I := 𝓡 n) (n := ∞) (x := x0))
      (fun z hz => hbase hz)).contDiffOn
  have hGJoint (i j : Fin n) : ContDiffOn ℝ ∞
      (Function.uncurry (fun s => G s i j)) (Ioo 0 T ×ˢ c.target) := by
    have hg := contMDiffOn_family_metric_pair F.smooth (E i) (E j) (hE i) (hE j)
    have hmap : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, V))
        (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
        (fun p : ℝ × V => (p.1, c.symm p.2)) (Ioo 0 T ×ˢ c.target) :=
      contMDiffOn_fst.prodMk
        ((contMDiffOn_chart_symm (I := 𝓡 n) (n := ∞) (x := x0)).comp
          contMDiffOn_snd (fun p hp => hp.2))
    have hh := hg.comp hmap (fun p hp => ⟨⟨hp.1.1.le, hp.1.2⟩, hbase hp.2⟩)
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hh
    exact hh.contDiffOn
  have hGSmooth (s : ℝ) (hs : s ∈ Ioo 0 T) (i j : Fin n) :
      ContDiffOn ℝ ∞ (G s i j) c.target :=
    (hGJoint i j).comp (contDiffOn_const.prodMk contDiffOn_id)
      (fun z hz => ⟨hs, hz⟩)
  have hfamily (s : ℝ) : RiemannianMetric.IsSmoothFamilyOn
      (fun _ : ℝ => F.metric s) Set.univ :=
    ((F.metric s).contMDiff.comp contMDiff_snd).contMDiffOn
  have hHSmooth (s : ℝ) (i j : Fin n) :
      ContDiffOn ℝ ∞ (H s i j) c.target := by
    have hInv : ContMDiffOn (𝓡 n) 𝓘(ℝ, (V →L[ℝ] ℝ) →L[ℝ] V) ∞
        (fun y => (A s y).inverse) e.baseSet :=
      (contMDiffOn_family_metric_frame_inverse (hfamily s) x0).2.2.comp
        (show ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
          (fun y : M => ((0 : ℝ), y)) e.baseSet from
          contMDiffOn_const.prodMk contMDiffOn_id)
        (fun y hy => ⟨Set.mem_univ (0 : ℝ), hy⟩)
    apply hchart (fun y => (EuclideanSpace.proj i : V →L[ℝ] ℝ)
      ((A s y).inverse (EuclideanSpace.proj j)))
    exact (EuclideanSpace.proj i : V →L[ℝ] ℝ).contMDiff.comp_contMDiffOn
      (hInv.clm_apply (contMDiffOn_const (c := EuclideanSpace.proj j)))
  have hLSmooth (r : ℕ) (s : ℝ) (alpha : Fin (r + 4) → Fin n) :
      ContDiffOn ℝ ∞ (L r s alpha) c.target := by
    apply hchart (fun y => (F.metric s).inner y
      (curvatureOnFields_iteratedCovariantDerivative (F.connection s) r
        (fun j : Fin (r + 3) => E (alpha j.castSucc)) y)
      (E (alpha (Fin.last (r + 3))) y))
    exact (contMDiffOn_family_metric_pair (hfamily s)
      (curvatureOnFields_iteratedCovariantDerivative (F.connection s) r
        (fun j : Fin (r + 3) => E (alpha j.castSucc)))
      (E (alpha (Fin.last (r + 3))))
      (contMDiffOn_curvatureOnFields_iteratedCovariantDerivative (F.connection s)
        e.open_baseSet r _ (fun j => hE (alpha j.castSucc)))
      (hE (alpha (Fin.last (r + 3))))).comp
      (show ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
        (fun y : M => ((0 : ℝ), y)) e.baseSet from
        contMDiffOn_const.prodMk contMDiffOn_id)
      (fun y hy => ⟨Set.mem_univ (0 : ℝ), hy⟩)
  have htrSmooth (s : ℝ) (i j : Fin n) : ContDiffOn ℝ ∞ (tr s i j) c.target :=
    ContDiffOn.sum (fun p _ => ContDiffOn.sum (fun q _ =>
      (hHSmooth s p q).mul (hLSmooth 0 s ![p,i,j,q])))
  have htimeRate (s : ℝ) (hs : s ∈ Ioo 0 T) (z : V) (hz : z ∈ c.target)
      (i j : Fin n) : HasDerivAt (fun r => G r i j z) (Q s i j z) s := by
    have hsint : s ∈ interior (Ico 0 T) := by simpa only [interior_Ico] using hs
    exact hasDerivAt_ricciFlow_metric_frame_coordinates F hsint x0 (c.symm z) (hbase hz) i j
  have hjetRate (q : ℕ) (s : ℝ) (hs : s ∈ Ico a T)
      (z : V) (hz : z ∈ c.target) (i j : Fin n) :
      HasDerivAt (fun r => iteratedFDeriv ℝ q (G r i j) z)
        (iteratedFDeriv ℝ q (Q s i j) z) s := by
    have hd := hasDerivAt_iteratedFDeriv_family isOpen_Ioo c.open_target
      (fun r => G r i j) (hGJoint i j) q (htime hs) hz
    have he : (fun y => deriv (fun r => G r i j y) s) =ᶠ[𝓝 z] Q s i j := by
      filter_upwards [c.open_target.mem_nhds hz] with y hy
      exact (htimeRate s (htime hs) y hy i j).deriv
    exact hd.congr_deriv (he.iteratedFDeriv (𝕜 := ℝ) q).eq_of_nhds
  have hsum {N : ℕ} (f : Fin N → V → ℝ)
      (hf : ∀ i, ContDiffOn ℝ ∞ (f i) c.target)
      (z : V) (hz : z ∈ c.target) (q : ℕ) (B : ℝ)
      (hb : ∀ i, ‖iteratedFDeriv ℝ q (f i) z‖ ≤ B) :
      ‖iteratedFDeriv ℝ q (fun y => ∑ i, f i y) z‖ ≤ (N : ℝ) * B := by
    rw [iteratedFDeriv_fun_sum_apply
      (fun i _ => ((hf i).contDiffAt (c.open_target.mem_nhds hz)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl q))]
    calc
      _ ≤ ∑ i : Fin N, ‖iteratedFDeriv ℝ q (f i) z‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin N, B := Finset.sum_le_sum (fun i _ => hb i)
      _ = (N : ℝ) * B := by simp
  intro m
  obtain ⟨BG, _, hBG, _, hGammaBound, _, _⟩ :=
    ricciFlow_connection_coordinate_jets_terminal_control hT F hRm ha haT x0 hK hKchart m
  obtain ⟨⟨BH, hBH, hHBound⟩, hLBound⟩ :=
    ricciFlow_inverse_and_lowered_coordinate_jets_of_connection_jets
      hT F hRm ha haT x0 hK hKchart m (by
        refine ⟨BG, hBG, ?_⟩
        intro q hq s hs z hz i j l
        exact hGammaBound q (Nat.le_of_lt hq) s hs z hz i j l)
  change ∀ q ≤ m, ∀ s ∈ Ico a T, ∀ z ∈ K, ∀ i j : Fin n,
    ‖iteratedFDeriv ℝ q (H s i j) z‖ ≤ BH at hHBound
  obtain ⟨BL, hBL, hL0Bound⟩ := hLBound 0
  change ∀ q ≤ m, ∀ s ∈ Ico a T, ∀ z ∈ K, ∀ alpha : Fin 4 → Fin n,
    ‖iteratedFDeriv ℝ q (L 0 s alpha) z‖ ≤ BL at hL0Bound
  let P := (2 : ℝ) ^ m * BH * BL
  let R := 2 * ((n : ℝ) * ((n : ℝ) * P))
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have htrBound (q : ℕ) (hq : q ≤ m) (s : ℝ) (hs : s ∈ Ico a T)
      (z : V) (hz : z ∈ K) (i j : Fin n) :
      ‖iteratedFDeriv ℝ q (tr s i j) z‖ ≤ (n : ℝ) * ((n : ℝ) * P) := by
    apply hsum _ (fun p => ContDiffOn.sum (fun v _ =>
      (hHSmooth s p v).mul (hLSmooth 0 s ![p,i,j,v]))) z (hKchart hz) q ((n : ℝ) * P)
    intro p
    apply hsum _ (fun v => (hHSmooth s p v).mul (hLSmooth 0 s ![p,i,j,v]))
      z (hKchart hz) q P
    intro v
    apply (norm_iteratedFDeriv_mul_le_of_open_bounds c.open_target
      (hHSmooth s p v) (hLSmooth 0 s ![p,i,j,v]) (hKchart hz) q hBH hBL
      (fun l hl => hHBound l (hl.trans hq) s hs z hz p v)
      (fun l hl => hL0Bound l (hl.trans hq) s hs z hz ![p,i,j,v])).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hq) hBH) hBL
  have hQBound (q : ℕ) (hq : q ≤ m) (s : ℝ) (hs : s ∈ Ico a T)
      (z : V) (hz : z ∈ K) (i j : Fin n) :
      ‖iteratedFDeriv ℝ q (Q s i j) z‖ ≤ R := by
    change ‖iteratedFDeriv ℝ q (fun y => (-2 : ℝ) • tr s i j y) z‖ ≤ R
    rw [iteratedFDeriv_const_smul_apply' (a := (-2 : ℝ))
      (((htrSmooth s i j).contDiffAt (c.open_target.mem_nhds (hKchart hz))).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl q)), norm_smul]
    rw [show ‖(-2 : ℝ)‖ = 2 by norm_num]
    exact mul_le_mul_of_nonneg_left (htrBound q hq s hs z hz i j) (by norm_num)
  have hinitial (q : Fin (m + 1)) (i j : Fin n) : ∃ B : ℝ, 0 ≤ B ∧
      ∀ z ∈ K, ‖iteratedFDeriv ℝ q.1 (G a i j) z‖ ≤ B := by
    have hc := ContinuousOn.continuousOn_iteratedFDeriv
      (hGSmooth a ⟨ha, haT⟩ i j) c.open_target
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl q.1)
    obtain ⟨B, hB⟩ := hK.bddAbove_image (hc.norm.mono hKchart)
    refine ⟨max B 0, le_max_right _ _, ?_⟩
    intro z hz
    exact (hB (mem_image_of_mem _ hz)).trans (le_max_left _ _)
  choose init hinitNonneg hinitBound using hinitial
  let B0 := ∑ q : Fin (m + 1), ∑ i : Fin n, ∑ j : Fin n, init q i j
  have hB0 : 0 ≤ B0 := Finset.sum_nonneg (fun q _ =>
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hinitNonneg q i j)))
  have hinitLe (q : Fin (m + 1)) (i j : Fin n) : init q i j ≤ B0 := by
    calc
      _ ≤ ∑ v : Fin n, init q i v :=
        Finset.single_le_sum (fun v _ => hinitNonneg q i v) (Finset.mem_univ j)
      _ ≤ ∑ u : Fin n, ∑ v : Fin n, init q u v :=
        Finset.single_le_sum (fun u _ => Finset.sum_nonneg
          (fun v _ => hinitNonneg q u v)) (Finset.mem_univ i)
      _ ≤ B0 := Finset.single_le_sum (fun p _ => Finset.sum_nonneg
        (fun u _ => Finset.sum_nonneg (fun v _ => hinitNonneg p u v))) (Finset.mem_univ q)
  have hinitialBound (q : ℕ) (hq : q ≤ m) (z : V) (hz : z ∈ K) (i j : Fin n) :
      ‖iteratedFDeriv ℝ q (G a i j) z‖ ≤ B0 :=
    (hinitBound ⟨q, Nat.lt_succ_of_le hq⟩ i j z hz).trans (hinitLe _ i j)
  have hLip (q : ℕ) (hq : q ≤ m) (s : ℝ) (hs : s ∈ Ico a T)
      (t : ℝ) (ht : t ∈ Ico a T) (z : V) (hz : z ∈ K) (i j : Fin n) :
      ‖iteratedFDeriv ℝ q (G t i j) z - iteratedFDeriv ℝ q (G s i j) z‖ ≤
        R * |t - s| := by
    have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun r hr => (hjetRate q r hr z (hKchart hz) i j).hasDerivWithinAt)
      (fun r hr => hQBound q hq r hr z hz i j) (convex_Ico a T) hs ht
    simpa only [Real.norm_eq_abs] using hh
  refine ⟨B0 + R * (T - a), R,
    add_nonneg hB0 (mul_nonneg hR (sub_nonneg.mpr haT.le)), hR, ?_, ?_, hLip⟩
  · intro q hq s hs z hz i j
    calc
      _ ≤ ‖iteratedFDeriv ℝ q (G a i j) z‖ +
          ‖iteratedFDeriv ℝ q (G s i j) z - iteratedFDeriv ℝ q (G a i j) z‖ :=
        norm_le_norm_add_norm_sub' _ _
      _ ≤ B0 + R * |s - a| := add_le_add (hinitialBound q hq z hz i j)
        (hLip q hq a haI s hs z hz i j)
      _ ≤ B0 + R * (T - a) := by
        rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
          (sub_le_sub_right hs.2.le a) hR)
  · intro q hq s hs z hz i j
    refine ⟨(hjetRate q s hs z (hKchart hz) i j).differentiableAt, ?_⟩
    rw [(hjetRate q s hs z (hKchart hz) i j).deriv]
    exact hQBound q hq s hs z hz i j

end TerminalCoordinates

end PoincareConjecture.Proofs.M03
