import PoincareConjecture.Proofs.M03.CurvatureExtension
import PoincareConjecture.Proofs.M03.CurvatureDifferenceTime
import Mathlib.Analysis.InnerProductSpace.Trace











set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle Manifold Set

universe u v

namespace PoincareConjecture.Proofs.M03

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem exists_curvatureEndomorphism {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (x : M) (u v : TangentSpace (𝓡 n) x) :
    ∃ A : TangentSpace (𝓡 n) x →ₗ[ℝ] TangentSpace (𝓡 n) x,
      (∀ w, A w = D.curvature x w u v) ∧
        D.ricci x u v = LinearMap.trace ℝ (TangentSpace (𝓡 n) x) A := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨V, hV, hv⟩ :=
    FiberBundle.exists_contMDiffOn_extend (k := ∞) (𝓡 n) (EuclideanSpace ℝ (Fin n)) v
  obtain ⟨S, hS, hSopen, hxS⟩ := mem_nhds_iff.mp hV
  have hT := curvatureOnFields_tensorial_first D hSopen
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) u)
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v) (hv.mono hS) hxS
  let A : TangentSpace (𝓡 n) x →ₗ[ℝ] TangentSpace (𝓡 n) x :=
    (TensorialAt.mkHom
      (fun X : (y : M) → TangentSpace (𝓡 n) y => D.curvatureOnFields X
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) u)
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v) x) x hT).toLinearMap
  have hA (w : TangentSpace (𝓡 n) x) : A w = D.curvature x w u v := rfl
  refine ⟨A, hA, ?_⟩
  let b := g.orthonormalBasis x
  rw [LinearMap.trace_eq_sum_inner A b]
  change (∑ i, g.inner x (D.curvature x u (b i) (b i)) v) =
    ∑ i, g.inner x (b i) (A (b i))
  obtain ⟨U, hU, hu⟩ :=
    FiberBundle.exists_contMDiffOn_extend (k := ∞) (𝓡 n) (EuclideanSpace ℝ (Fin n)) u
  apply Finset.sum_congr rfl
  intro i _
  obtain ⟨B, hB, hb⟩ :=
    FiberBundle.exists_contMDiffOn_extend (k := ∞) (𝓡 n) (EuclideanSpace ℝ (Fin n)) (b i)
  obtain ⟨T, hTsub, hTopen, hxT⟩ :=
    mem_nhds_iff.mp (Filter.inter_mem hU (Filter.inter_mem hB hV))
  have hskew := curvatureOnFields_pair_skew D hTopen
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) u)
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (b i))
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (b i))
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v)
    (hu.mono fun _ hy => (hTsub hy).1)
    (hb.mono fun _ hy => (hTsub hy).2.1)
    (hb.mono fun _ hy => (hTsub hy).2.1)
    (hv.mono fun _ hy => (hTsub hy).2.2) hxT
  simp only [FiberBundle.extend_apply_self] at hskew
  change g.inner x (D.curvature x u (b i) (b i)) v =
    -g.inner x (b i) (D.curvature x u (b i) v) at hskew
  rw [hskew, hA]
  have hswap : D.curvature x u (b i) v = -D.curvature x (b i) u v := by
    delta LeviCivitaData.curvature
    exact curvatureOnFields_swap D _ _ _ x
  rw [hswap, map_neg, neg_neg]

theorem ricci_eq_sum_basis {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (x : M) (u v : TangentSpace (𝓡 n) x)
    {ι : Type v} [Fintype ι] (b : Module.Basis ι ℝ (TangentSpace (𝓡 n) x)) :
    D.ricci x u v = ∑ i, b.repr (D.curvature x (b i) u v) i := by
  classical
  obtain ⟨A, hA, hRic⟩ := exists_curvatureEndomorphism D x u v
  rw [hRic, LinearMap.trace_eq_matrix_trace ℝ b A]
  change (∑ i, LinearMap.toMatrix b b A i i) = _
  apply Finset.sum_congr rfl
  intro i _
  rw [LinearMap.toMatrix_apply, hA]

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 200000 in
set_option maxRecDepth 2000 in
theorem ricciFlow_curvature_derivative_reaction_pairing_le
    {I : Set ℝ} (F : RicciFlow n M I) {t : ℝ} (ht : t ∈ interior I)
    (x0 : M) {x : M}
    (hx : x ∈ (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)) x0).baseSet) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric 0).toRiemannianMetric⟩
    let V := EuclideanSpace ℝ (Fin n)
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let E := e.localFrame (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let G := ContinuousLinearMap.inCoordinates V
      (TangentSpace (𝓡 n)) (V →L[ℝ] ℝ)
      (fun z => TangentSpace (𝓡 n) z →L[ℝ] ℝ) x0 x x0 x ((F.metric t).inner x)
    let a := fun i j : Fin n => (G.inverse (EuclideanSpace.proj j)) i
    let N := fun s (P Q : (y : M) → TangentSpace (𝓡 n) y) y =>
      (F.connection s).connection Q y (P y)
    let R := fun s (A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
      (F.connection s).curvatureOnFields A B C y
    let K := fun s (P A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
      N s P (R s A B C) y - R s (N s P A) B C y -
        R s A (N s P B) C y - R s A B (N s P C) y
    let H := fun (P Q A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
      N t P (K t Q A B C) y - K t (N t P Q) A B C y -
        K t Q (N t P A) B C y - K t Q A (N t P B) C y - K t Q A B (N t P C) y
    let J := fun (P Q A B C W : (y : M) → TangentSpace (𝓡 n) y) y =>
      N t P (H Q A B C W) y - H (N t P Q) A B C W y -
        H Q (N t P A) B C W y - H Q A (N t P B) C W y -
        H Q A B (N t P C) W y - H Q A B C (N t P W) y
    let pair := fun (v w : (Fin 4 → Fin n) → TangentSpace (𝓡 n) x) =>
      ∑ α, ∑ β, (∏ r, a (α r) (β r)) * (F.metric t).inner x (v α) (w β)
    let k := fun s (α : Fin 4 → Fin n) =>
      K s (E (α 0)) (E (α 1)) (E (α 2)) (E (α 3)) x
    2 * pair (fun α => deriv (fun s => k s α) t -
      ∑ i, ∑ j, a i j • J (E i) (E j) (E (α 0)) (E (α 1)) (E (α 2)) (E (α 3)) x)
        (k t) ≤
      86 * (n : ℝ) ^ 3 * (F.connection t).curvatureTensorNorm x * pair (k t) (k t) := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric 0).toRiemannianMetric⟩
  let : IsManifold (𝓡 n) (∞ + 1) M := by
    simpa using (inferInstance : IsManifold (𝓡 n) ∞ M)
  let : IsManifold (𝓡 n) (minSmoothness ℝ 2) M :=
    IsManifold.of_le (n := ∞) (by
      simpa only [minSmoothness_of_isRCLikeNormedField] using
        (ENat.LEInfty.out (m := (2 : ℕ∞ω))))
  let : ContMDiffMul 𝓘(ℝ, ℝ) ∞ ℝ :=
    { contMDiff_mul := by
        rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
        exact contDiff_mul.contMDiff }
  let V := EuclideanSpace ℝ (Fin n)
  let g := F.metric t
  let D := F.connection t
  let e := trivializationAt V (TangentSpace (𝓡 n)) x0
  let cb := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let E := e.localFrame cb
  let theta := e.localFrameCoeff (𝓡 n) cb
  let G := ContinuousLinearMap.inCoordinates V
    (TangentSpace (𝓡 n)) (V →L[ℝ] ℝ)
    (fun z => TangentSpace (𝓡 n) z →L[ℝ] ℝ) x0 x x0 x (g.inner x)
  let a := fun i j : Fin n => (G.inverse (EuclideanSpace.proj j)) i
  let N := fun s (P Q : (y : M) → TangentSpace (𝓡 n) y) y =>
    (F.connection s).connection Q y (P y)
  let R := fun s (A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
    (F.connection s).curvatureOnFields A B C y
  let K := fun s (P A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
    N s P (R s A B C) y - R s (N s P A) B C y -
      R s A (N s P B) C y - R s A B (N s P C) y
  let H := fun (P Q A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
    N t P (K t Q A B C) y - K t (N t P Q) A B C y -
      K t Q (N t P A) B C y - K t Q A (N t P B) C y - K t Q A B (N t P C) y
  let J := fun (P Q A B C W : (y : M) → TangentSpace (𝓡 n) y) y =>
    N t P (H Q A B C W) y - H (N t P Q) A B C W y -
      H Q (N t P A) B C W y - H Q A (N t P B) C W y -
      H Q A B (N t P C) W y - H Q A B C (N t P W) y
  let Btime := fun (P Q : (y : M) → TangentSpace (𝓡 n) y) y =>
    deriv (fun s => N s P Q y) t
  let k := fun s (α : Fin 4 → Fin n) =>
    K s (E (α 0)) (E (α 1)) (E (α 2)) (E (α 3)) x
  let z := fun (α : Fin 4 → Fin n) => deriv (fun s => k s α) t -
    ∑ i, ∑ j, a i j • J (E i) (E j) (E (α 0)) (E (α 1)) (E (α 2)) (E (α 3)) x
  let W := fun (α β : Fin 4 → Fin n) => ∏ r, a (α r) (β r)
  let pair := fun (v w : (Fin 4 → Fin n) → TangentSpace (𝓡 n) x) =>
    ∑ α, ∑ β, W α β * g.inner x (v α) (w β)
  change 2 * pair z (k t) ≤ 86 * (n : ℝ) ^ 3 * D.curvatureTensorNorm x * pair (k t) (k t)
  let S := fun P : (y : M) → TangentSpace (𝓡 n) y =>
    ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% P) e.baseSet
  have hE (i : Fin n) : S (E i) :=
    e.contMDiffOn_localFrame_baseSet (I := 𝓡 n) ∞ cb i
  have hsN (P Q : (y : M) → TangentSpace (𝓡 n) y) (hP : S P) (hQ : S Q) :
      S (N t P Q) := D.contMDiffOn_connection_apply e.open_baseSet P Q hP hQ
  have hsR (P Q Z : (y : M) → TangentSpace (𝓡 n) y)
      (hP : S P) (hQ : S Q) (hZ : S Z) : S (R t P Q Z) := by
    have hbr : S (VectorField.mlieBracket (𝓡 n) P Q) := by
      intro y hy
      exact ((hP.contMDiffAt (e.open_baseSet.mem_nhds hy)).mlieBracket_vectorField
        (hQ.contMDiffAt (e.open_baseSet.mem_nhds hy)) (m := ⊤) (n := ⊤)
        (by simp)).contMDiffWithinAt
    exact ((hsN P _ hP (hsN Q Z hQ hZ)).sub_section
      (hsN Q _ hQ (hsN P Z hP hZ))).sub_section (hsN _ Z hbr hZ)
  have hsK (P A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hP : S P) (hA : S A) (hB : S B) (hC : S C) : S (K t P A B C) :=
    (((hsN P _ hP (hsR A B C hA hB hC)).sub_section
      (hsR _ B C (hsN P A hP hA) hB hC)).sub_section
      (hsR A _ C hA (hsN P B hP hB) hC)).sub_section
      (hsR A B _ hA hB (hsN P C hP hC))
  have hsB (P Q : (y : M) → TangentSpace (𝓡 n) y) (hP : S P) (hQ : S Q) :
      S (Btime P Q) :=
    (family_tangent_time_derivative (F.metric 0) e.open_baseSet (fun s => N s P Q)
      (contMDiffOn_connection_family_apply F.smooth F.connection e.open_baseSet
        Q P hQ hP) ht).2
  obtain ⟨R0, hR0⟩ := exists_curvature_trilinearMap D x
  obtain ⟨T, hT⟩ := exists_curvatureOnFields_derivative_quadrilinearMap D x
  obtain ⟨B0, hB0⟩ := exists_ricciFlow_connection_variation_bilinearMap F ht x
  have hRf (P Q Z : (y : M) → TangentSpace (𝓡 n) y)
      (hP : S P) (hQ : S Q) (hZ : S Z) : R t P Q Z x = R0 (P x) (Q x) (Z x) :=
    (curvature_eq_curvatureOnFields D e.open_baseSet P Q Z hP hQ hZ hx).symm.trans
      (hR0 (P x) (Q x) (Z x)).symm
  have hTf (P A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hP : S P) (hA : S A) (hB : S B) (hC : S C) :
      K t P A B C x = T (P x) (A x) (B x) (C x) :=
    (hT e.open_baseSet P A B C hP hA hB hC hx).symm
  have hBf (P Q : (y : M) → TangentSpace (𝓡 n) y) (hP : S P) (hQ : S Q) :
      Btime P Q x = B0 (P x) (Q x) :=
    (hB0 e.open_baseSet P Q hP hQ hx).symm
  let Co := fun (P X Y A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
    R t P X (K t Y A B C) y - K t (R t P X Y) A B C y -
      K t Y (R t P X A) B C y - K t Y A (R t P X B) C y - K t Y A B (R t P X C) y +
      K t X P Y (R t A B C) y + R t P Y (K t X A B C) y -
      K t X (R t P Y A) B C y - R t (K t X P Y A) B C y -
      K t X A (R t P Y B) C y - R t A (K t X P Y B) C y -
      K t X A B (R t P Y C) y - R t A B (K t X P Y C) y
  let DZ := fun (P A B C X Y : (y : M) → TangentSpace (𝓡 n) y) y =>
    K t P (R t A B X) Y C y + R t (K t P A B X) Y C y -
      (2 : ℝ) • K t P B X (R t Y A C) y - (2 : ℝ) • R t B X (K t P Y A C) y +
      (2 : ℝ) • K t P X A (R t B Y C) y + (2 : ℝ) • R t X A (K t P B Y C) y +
      K t P (R t A B C) X Y y + R t (K t P A B C) X Y y -
      K t P (R t A X Y) B C y - R t (K t P A X Y) B C y -
      K t P A (R t B X Y) C y - R t A (K t P B X Y) C y -
      K t P A B (R t C X Y) y - R t A B (K t P C X Y) y
  let Co0 := fun (p u v a b c : TangentSpace (𝓡 n) x) =>
    R0 p u (T v a b c) - T (R0 p u v) a b c -
      T v (R0 p u a) b c - T v a (R0 p u b) c - T v a b (R0 p u c) +
      T u p v (R0 a b c) + R0 p v (T u a b c) -
      T u (R0 p v a) b c - R0 (T u p v a) b c -
      T u a (R0 p v b) c - R0 a (T u p v b) c -
      T u a b (R0 p v c) - R0 a b (T u p v c)
  let DZ0 := fun (p a b c u v : TangentSpace (𝓡 n) x) =>
    T p (R0 a b u) v c + R0 (T p a b u) v c -
      (2 : ℝ) • T p b u (R0 v a c) - (2 : ℝ) • R0 b u (T p v a c) +
      (2 : ℝ) • T p u a (R0 b v c) + (2 : ℝ) • R0 u a (T p b v c) +
      T p (R0 a b c) u v + R0 (T p a b c) u v -
      T p (R0 a u v) b c - R0 (T p a u v) b c -
      T p a (R0 b u v) c - R0 a (T p b u v) c -
      T p a b (R0 c u v) - R0 a b (T p c u v)
  have hCo (P X Y A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hP : S P) (hX : S X) (hY : S Y) (hA : S A) (hB : S B) (hC : S C) :
      Co P X Y A B C x = Co0 (P x) (X x) (Y x) (A x) (B x) (C x) := by
    simp only [Co, Co0, hRf, hTf, hsR, hsK, hP, hX, hY, hA, hB, hC]
  have hDZ (P A B C X Y : (y : M) → TangentSpace (𝓡 n) y)
      (hP : S P) (hA : S A) (hB : S B) (hC : S C) (hX : S X) (hY : S Y) :
      DZ P A B C X Y x = DZ0 (P x) (A x) (B x) (C x) (X x) (Y x) := by
    simp only [DZ, DZ0, hRf, hTf, hsR, hsK, hP, hX, hY, hA, hB, hC]
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let ι := Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))
  let b := g.orthonormalBasis x
  have hrec (v : TangentSpace (𝓡 n) x) :
      v = ∑ i : Fin n, theta i x v • E i x := by
    simpa only [FiberBundle.extend_apply_self] using
      e.eq_sum_localFrameCoeff_smul (I := 𝓡 n) (b := cb)
        (s := FiberBundle.extend V v) hx
  have htrace (i j : Fin n) : a i j =
      ∑ r, theta i x (b r) * theta j x (b r) :=
    metric_inverse_eq_sum_orthonormal_coordinates g x0 x hx i j
  have hcontract (Z : TangentSpace (𝓡 n) x →ₗ[ℝ]
      TangentSpace (𝓡 n) x →ₗ[ℝ] TangentSpace (𝓡 n) x) :
      (∑ i, ∑ j, a i j • Z (E i x) (E j x)) = ∑ r : ι, Z (b r) (b r) := by
    have hbilin (v w : TangentSpace (𝓡 n) x) :
        Z v w = ∑ i : Fin n, ∑ j : Fin n,
          (theta i x v * theta j x w) • Z (E i x) (E j x) := by
      nth_rw 1 [hrec v]
      rw [map_sum, LinearMap.sum_apply]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul, LinearMap.smul_apply]
      nth_rw 1 [hrec w]
      rw [map_sum, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [map_smul, smul_smul]
    symm
    calc
      _ = ∑ r : ι, ∑ i : Fin n, ∑ j : Fin n,
          (theta i x (b r) * theta j x (b r)) • Z (E i x) (E j x) :=
        Finset.sum_congr rfl (fun r _ => hbilin (b r) (b r))
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        rw [← Finset.sum_smul, ← htrace]
  let V0 := fun (p a b' c : TangentSpace (𝓡 n) x) =>
    (∑ r : ι, (Co0 p (b r) (b r) a b' c + DZ0 p a b' c (b r) (b r))) +
      B0 p (R0 a b' c) - R0 (B0 p a) b' c - R0 a (B0 p b') c - R0 a b' (B0 p c)
  have htraced (p a' b' c : TangentSpace (𝓡 n) x) :
      (∑ i, ∑ j, a i j • (Co0 p (E i x) (E j x) a' b' c +
        DZ0 p a' b' c (E i x) (E j x))) =
        ∑ r : ι, (Co0 p (b r) (b r) a' b' c + DZ0 p a' b' c (b r) (b r)) := by
    let Z := LinearMap.mk₂ ℝ
      (fun u v => Co0 p u v a' b' c + DZ0 p a' b' c u v)
      (by
        intro u u' v
        simp only [Co0, DZ0, map_add, LinearMap.add_apply, smul_add]
        module)
      (by
        intro s u v
        simp only [Co0, DZ0, map_smul, LinearMap.smul_apply, smul_add, smul_sub,
          smul_smul]
        module)
      (by
        intro u v v'
        simp only [Co0, DZ0, map_add, LinearMap.add_apply, smul_add]
        module)
      (by
        intro s u v
        simp only [Co0, DZ0, map_smul, LinearMap.smul_apply, smul_add, smul_sub,
          smul_smul]
        module)
    exact hcontract Z
  have hz (α : Fin 4 → Fin n) :
      z α = V0 (E (α 0) x) (E (α 1) x) (E (α 2) x) (E (α 3) x) := by
    have hp := ricciFlow_curvature_derivative_diffusion_reaction_localFrame F ht x0 hx
      (E (α 0)) (E (α 1)) (E (α 2)) (E (α 3))
      (hE (α 0)) (hE (α 1)) (hE (α 2)) (hE (α 3))
    change z α = (∑ i, ∑ j, a i j •
      (Co (E (α 0)) (E i) (E j) (E (α 1)) (E (α 2)) (E (α 3)) x +
        DZ (E (α 0)) (E (α 1)) (E (α 2)) (E (α 3)) (E i) (E j) x)) +
      Btime (E (α 0)) (R t (E (α 1)) (E (α 2)) (E (α 3))) x -
      R t (Btime (E (α 0)) (E (α 1))) (E (α 2)) (E (α 3)) x -
      R t (E (α 1)) (Btime (E (α 0)) (E (α 2))) (E (α 3)) x -
      R t (E (α 1)) (E (α 2)) (Btime (E (α 0)) (E (α 3))) x at hp
    simp only [hCo, hDZ, hRf, hBf, hsR, hsB, hE] at hp
    rw [htraced] at hp
    exact hp
  let LT : MultilinearMap ℝ (fun _ : Fin 4 => TangentSpace (𝓡 n) x)
      (TangentSpace (𝓡 n) x) :=
    MultilinearMap.mk' (fun v => T (v 0) (v 1) (v 2) (v 3))
      (by intro v i u w; fin_cases i <;> simp [map_add, LinearMap.add_apply])
      (by intro v i c u; fin_cases i <;> simp [map_smul, LinearMap.smul_apply])
  have hsmulTrace (v : Fin 4 → TangentSpace (𝓡 n) x) (i : Fin 4)
      (c : ℝ) (u : TangentSpace (𝓡 n) x) :
      (∑ r : ι, (Co0 ((Function.update v i (c • u)) 0) (b r) (b r)
          ((Function.update v i (c • u)) 1) ((Function.update v i (c • u)) 2)
          ((Function.update v i (c • u)) 3) +
        DZ0 ((Function.update v i (c • u)) 0) ((Function.update v i (c • u)) 1)
          ((Function.update v i (c • u)) 2) ((Function.update v i (c • u)) 3)
          (b r) (b r))) =
        c • ∑ r : ι, (Co0 ((Function.update v i u) 0) (b r) (b r)
          ((Function.update v i u) 1) ((Function.update v i u) 2)
          ((Function.update v i u) 3) +
        DZ0 ((Function.update v i u) 0) ((Function.update v i u) 1)
          ((Function.update v i u) 2) ((Function.update v i u) 3) (b r) (b r)) := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro r _
    fin_cases i <;>
      simp [Co0, DZ0, map_smul, LinearMap.smul_apply, smul_add, smul_sub,
        smul_smul] <;> module
  let LV : MultilinearMap ℝ (fun _ : Fin 4 => TangentSpace (𝓡 n) x)
      (TangentSpace (𝓡 n) x) :=
    MultilinearMap.mk' (fun v => V0 (v 0) (v 1) (v 2) (v 3))
      (by
        intro v i u w
        fin_cases i <;>
          simp [V0, Co0, DZ0, map_add, LinearMap.add_apply,
            smul_add, Finset.sum_add_distrib] <;> module)
      (by
        intro v i c u
        dsimp only [V0]
        rw [hsmulTrace]
        fin_cases i <;>
          simp [map_smul, LinearMap.smul_apply, smul_add, smul_sub])
  let d := fun (γ : Fin 4 → ι) (α : Fin 4 → Fin n) =>
    ∏ r, theta (α r) x (b (γ r))
  have hExpand (L : MultilinearMap ℝ (fun _ : Fin 4 => TangentSpace (𝓡 n) x)
      (TangentSpace (𝓡 n) x)) (γ : Fin 4 → ι) :
      L (fun r => b (γ r)) = ∑ α : Fin 4 → Fin n,
        d γ α • L (fun r => E (α r) x) := by
    calc
      _ = L (fun r => ∑ i : Fin n, theta i x (b (γ r)) • E i x) :=
        congrArg L (funext fun r => hrec (b (γ r)))
      _ = ∑ α : Fin 4 → Fin n,
          L (fun r => theta (α r) x (b (γ r)) • E (α r) x) :=
        L.map_sum (fun r i => theta i x (b (γ r)) • E i x)
      _ = _ := by simp only [MultilinearMap.map_smul_univ, d]
  have hWeight (α β : Fin 4 → Fin n) : W α β =
      ∑ γ : Fin 4 → ι, d γ α * d γ β := by
    dsimp only [W]
    simp_rw [htrace]
    rw [Fintype.prod_sum]
    simp only [d, Finset.prod_mul_distrib]
    rfl
  have hPair (v w : (Fin 4 → Fin n) → TangentSpace (𝓡 n) x) :
      pair v w = ∑ γ : Fin 4 → ι,
        g.inner x (∑ α, d γ α • v α) (∑ β, d γ β • w β) := by
    dsimp only [pair]
    rw [Finset.sum_comm]
    symm
    simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro β _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro α _
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul, hWeight]
    congr 1
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  have hTk (α : Fin 4 → Fin n) : LT (fun r => E (α r) x) = k t α :=
    hT e.open_baseSet (E (α 0)) (E (α 1)) (E (α 2)) (E (α 3))
      (hE (α 0)) (hE (α 1)) (hE (α 2)) (hE (α 3)) hx
  have hVz (α : Fin 4 → Fin n) : LV (fun r => E (α r) x) = z α := (hz α).symm
  have hpairIntrinsic : pair z (k t) = ∑ γ : Fin 4 → ι,
      g.inner x (LV (fun r => b (γ r))) (LT (fun r => b (γ r))) := by
    rw [hPair]
    simp only [← hVz, ← hTk, ← hExpand]
  let e0 := trivializationAt V (TangentSpace (𝓡 n)) x
  let ext := fun v : TangentSpace (𝓡 n) x => FiberBundle.extend V v
  have hx0 : x ∈ e0.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have hExt (v : TangentSpace (𝓡 n) x) : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, V)) ∞ (T% (ext v)) e0.baseSet := by
    have hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, V) ∞
        (fun _y : M => (e0 ⟨x, v⟩).2) e0.baseSet := contMDiffOn_const
    have hec : ContMDiffOn (𝓡 n) 𝓘(ℝ, V) ∞
        (fun y => (e0 ⟨y, ext v y⟩).2) e0.baseSet := by
      apply hc.congr
      intro y hy
      change (e0 ⟨y, e0.symm y (e0 ⟨x, v⟩).2⟩).2 = (e0 ⟨x, v⟩).2
      simpa only using congrArg Prod.snd (e0.apply_mk_symm hy (e0 ⟨x, v⟩).2)
    intro y hy
    rw [e0.contMDiffWithinAt_section _ hy]
    exact hec y hy
  let kb := fun γ : Fin 4 → ι =>
    K t (ext (b (γ 0))) (ext (b (γ 1))) (ext (b (γ 2))) (ext (b (γ 3))) x
  let Q := ∑ γ : Fin 4 → ι, g.inner x (kb γ) (kb γ)
  let A0 := D.curvatureTensorNorm x
  let L0 := Real.sqrt Q
  have hq : pair (k t) (k t) = Q :=
    curvature_derivative_squared_norm_frame_eq_orthonormal D x0 hx
  have hself (v : TangentSpace (𝓡 n) x) : g.inner x v v = ‖v‖ ^ 2 :=
    real_inner_self_eq_norm_sq v
  have hnorm (v : TangentSpace (𝓡 n) x) : g.tangentNorm x v = ‖v‖ := by
    rw [RiemannianMetric.tangentNorm, hself, Real.sqrt_sq (norm_nonneg _)]
  have hkb (γ : Fin 4 → ι) : LT (fun r => b (γ r)) = kb γ := by
    have hh := hT e0.open_baseSet (ext (b (γ 0))) (ext (b (γ 1)))
      (ext (b (γ 2))) (ext (b (γ 3))) (hExt _) (hExt _) (hExt _) (hExt _) hx0
    change T (ext (b (γ 0)) x) (ext (b (γ 1)) x)
      (ext (b (γ 2)) x) (ext (b (γ 3)) x) = kb γ at hh
    change T (b (γ 0)) (b (γ 1)) (b (γ 2)) (b (γ 3)) = kb γ
    simpa only [ext, FiberBundle.extend_apply_self] using hh
  have hQnorm : Q = ∑ γ : Fin 4 → ι, ‖LT (fun r => b (γ r))‖ ^ 2 := by
    simp only [Q, hself, hkb]
  have hQnonneg : 0 ≤ Q := by rw [hQnorm]; positivity
  have hL0 : 0 ≤ L0 := Real.sqrt_nonneg _
  have hA0 : 0 ≤ A0 := Real.sqrt_nonneg _
  have hLsq : L0 ^ 2 = Q := Real.sq_sqrt hQnonneg
  have hRn (u v w : TangentSpace (𝓡 n) x) :
      ‖R0 u v w‖ ≤ A0 * ‖u‖ * ‖v‖ * ‖w‖ := by
    have hh := curvature_tangentNorm_le_curvatureTensorNorm D x u v w
    rw [← hR0 u v w] at hh
    change g.tangentNorm x (R0 u v w) ≤
      A0 * g.tangentNorm x u * g.tangentNorm x v * g.tangentNorm x w at hh
    simpa only [hnorm] using hh
  have hTn (p a b' c : TangentSpace (𝓡 n) x) :
      ‖T p a b' c‖ ≤ L0 * ‖p‖ * ‖a‖ * ‖b'‖ * ‖c‖ := by
    have hh := curvature_derivative_tangentNorm_le_orthonormal_energy D e0.open_baseSet
      (ext p) (ext a) (ext b') (ext c) (hExt p) (hExt a) (hExt b') (hExt c) hx0
    have he := hT e0.open_baseSet (ext p) (ext a) (ext b') (ext c)
      (hExt p) (hExt a) (hExt b') (hExt c) hx0
    change T (ext p x) (ext a x) (ext b' x) (ext c x) =
      K t (ext p) (ext a) (ext b') (ext c) x at he
    have he' : T p a b' c = K t (ext p) (ext a) (ext b') (ext c) x := by
      simpa only [ext, FiberBundle.extend_apply_self] using he
    change g.tangentNorm x (K t (ext p) (ext a) (ext b') (ext c) x) ≤
      L0 * g.tangentNorm x (ext p x) * g.tangentNorm x (ext a x) *
        g.tangentNorm x (ext b' x) * g.tangentNorm x (ext c x) at hh
    rw [← he'] at hh
    simpa only [ext, FiberBundle.extend_apply_self, hnorm] using hh
  have hBn (u v : TangentSpace (𝓡 n) x) :
      ‖B0 u v‖ ≤ 3 * (n : ℝ) * L0 * ‖u‖ * ‖v‖ := by
    have hh := ricciFlow_connection_variation_tangentNorm_le_curvature_derivative_energy
      F ht e0.open_baseSet (ext u) (ext v) (hExt u) (hExt v) hx0
    have he := hB0 e0.open_baseSet (ext u) (ext v) (hExt u) (hExt v) hx0
    change B0 (ext u x) (ext v x) = Btime (ext u) (ext v) x at he
    have he' : B0 u v = Btime (ext u) (ext v) x := by
      simpa only [ext, FiberBundle.extend_apply_self] using he
    change g.tangentNorm x (Btime (ext u) (ext v) x) ≤
      3 * (n : ℝ) * L0 * g.tangentNorm x (ext u x) * g.tangentNorm x (ext v x) at hh
    rw [← he'] at hh
    simpa only [ext, FiberBundle.extend_apply_self, hnorm] using hh
  have hdim : Fintype.card ι = n := by
    simp only [ι, Fintype.card_fin]
    rw [VectorBundle.finrank_eq ℝ V (TangentSpace (𝓡 n)) x, finrank_euclideanSpace_fin]
  have hpoly (p X Y a b' c : TangentSpace (𝓡 n) x)
      (hp : ‖p‖ = 1) (hX : ‖X‖ = 1) (hY : ‖Y‖ = 1)
      (ha : ‖a‖ = 1) (hb : ‖b'‖ = 1) (hc : ‖c‖ = 1) :
      ‖Co0 p X Y a b' c‖ ≤ 13 * A0 * L0 ∧ ‖DZ0 p a b' c X Y‖ ≤ 18 * A0 * L0 := by
    dsimp only [Co0, DZ0]
    let m := A0 * L0
    have hRunit (u v w : TangentSpace (𝓡 n) x)
        (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) : ‖R0 u v w‖ ≤ A0 := by
      simpa only [hu, hv, hw, mul_one] using hRn u v w
    have hTunit (u v w z : TangentSpace (𝓡 n) x) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
        (hw : ‖w‖ = 1) (hz : ‖z‖ = 1) : ‖T u v w z‖ ≤ L0 := by
      simpa only [hu, hv, hw, hz, mul_one] using hTn u v w z
    have hRcomp (u v w : TangentSpace (𝓡 n) x)
        (h : ‖u‖ * ‖v‖ * ‖w‖ ≤ L0) : ‖R0 u v w‖ ≤ m := by
      calc
        _ ≤ A0 * ‖u‖ * ‖v‖ * ‖w‖ := hRn u v w
        _ = A0 * (‖u‖ * ‖v‖ * ‖w‖) := by ring
        _ ≤ m := mul_le_mul_of_nonneg_left h hA0
    have hTcomp (u v w z : TangentSpace (𝓡 n) x)
        (h : ‖u‖ * ‖v‖ * ‖w‖ * ‖z‖ ≤ A0) : ‖T u v w z‖ ≤ m := by
      calc
        _ ≤ L0 * ‖u‖ * ‖v‖ * ‖w‖ * ‖z‖ := hTn u v w z
        _ = L0 * (‖u‖ * ‖v‖ * ‖w‖ * ‖z‖) := by ring
        _ ≤ L0 * A0 := mul_le_mul_of_nonneg_left h hL0
        _ = m := mul_comm _ _
    have hCo1 : ‖R0 p X (T Y a b' c)‖ ≤ m :=
      hRcomp _ _ _ (by simpa only [hp, hX, one_mul] using hTunit Y a b' c hY ha hb hc)
    have hCo2 : ‖T (R0 p X Y) a b' c‖ ≤ m :=
      hTcomp _ _ _ _ (by simpa only [ha, hb, hc, mul_one] using hRunit p X Y hp hX hY)
    have hCo3 : ‖T Y (R0 p X a) b' c‖ ≤ m :=
      hTcomp _ _ _ _ (by simpa only [hY, hb, hc, one_mul, mul_one] using hRunit p X a hp hX ha)
    have hCo4 : ‖T Y a (R0 p X b') c‖ ≤ m :=
      hTcomp _ _ _ _ (by simpa only [hY, ha, hc, one_mul, mul_one] using hRunit p X b' hp hX hb)
    have hCo5 : ‖T Y a b' (R0 p X c)‖ ≤ m :=
      hTcomp _ _ _ _ (by simpa only [hY, ha, hb, one_mul] using hRunit p X c hp hX hc)
    have hCo6 : ‖T X p Y (R0 a b' c)‖ ≤ m :=
      hTcomp _ _ _ _ (by simpa only [hX, hp, hY, one_mul] using hRunit a b' c ha hb hc)
    have hCo7 : ‖R0 p Y (T X a b' c)‖ ≤ m :=
      hRcomp _ _ _ (by simpa only [hp, hY, one_mul] using hTunit X a b' c hX ha hb hc)
    have hCo8 : ‖T X (R0 p Y a) b' c‖ ≤ m :=
      hTcomp _ _ _ _ (by simpa only [hX, hb, hc, one_mul, mul_one] using hRunit p Y a hp hY ha)
    have hCo9 : ‖R0 (T X p Y a) b' c‖ ≤ m :=
      hRcomp _ _ _ (by simpa only [hb, hc, mul_one] using hTunit X p Y a hX hp hY ha)
    have hCo10 : ‖T X a (R0 p Y b') c‖ ≤ m :=
      hTcomp _ _ _ _ (by simpa only [hX, ha, hc, one_mul, mul_one] using hRunit p Y b' hp hY hb)
    have hCo11 : ‖R0 a (T X p Y b') c‖ ≤ m :=
      hRcomp _ _ _ (by simpa only [ha, hc, one_mul, mul_one] using hTunit X p Y b' hX hp hY hb)
    have hCo12 : ‖T X a b' (R0 p Y c)‖ ≤ m :=
      hTcomp _ _ _ _ (by simpa only [hX, ha, hb, one_mul] using hRunit p Y c hp hY hc)
    have hCo13 : ‖R0 a b' (T X p Y c)‖ ≤ m :=
      hRcomp _ _ _ (by simpa only [ha, hb, one_mul] using hTunit X p Y c hX hp hY hc)
    have hDZ1 : ‖T p (R0 a b' X) Y c‖ ≤ m :=
      hTcomp _ _ _ _ (by simpa only [hp, hY, hc, one_mul, mul_one] using hRunit a b' X ha hb hX)
    have hDZ2 : ‖R0 (T p a b' X) Y c‖ ≤ m :=
      hRcomp _ _ _ (by simpa only [hY, hc, mul_one] using hTunit p a b' X hp ha hb hX)
    have hDZ3 : ‖T p b' X (R0 Y a c)‖ ≤ m :=
      hTcomp _ _ _ _ (by simpa only [hp, hb, hX, one_mul] using hRunit Y a c hY ha hc)
    have hDZ4 : ‖R0 b' X (T p Y a c)‖ ≤ m :=
      hRcomp _ _ _ (by simpa only [hb, hX, one_mul] using hTunit p Y a c hp hY ha hc)
    have hDZ5 : ‖T p X a (R0 b' Y c)‖ ≤ m :=
      hTcomp _ _ _ _ (by simpa only [hp, hX, ha, one_mul] using hRunit b' Y c hb hY hc)
    have hDZ6 : ‖R0 X a (T p b' Y c)‖ ≤ m :=
      hRcomp _ _ _ (by simpa only [hX, ha, one_mul] using hTunit p b' Y c hp hb hY hc)
    have hDZ7 : ‖T p (R0 a b' c) X Y‖ ≤ m :=
      hTcomp _ _ _ _ (by simpa only [hp, hX, hY, one_mul, mul_one] using hRunit a b' c ha hb hc)
    have hDZ8 : ‖R0 (T p a b' c) X Y‖ ≤ m :=
      hRcomp _ _ _ (by simpa only [hX, hY, mul_one] using hTunit p a b' c hp ha hb hc)
    have hDZ9 : ‖T p (R0 a X Y) b' c‖ ≤ m :=
      hTcomp _ _ _ _ (by simpa only [hp, hb, hc, one_mul, mul_one] using hRunit a X Y ha hX hY)
    have hDZ10 : ‖R0 (T p a X Y) b' c‖ ≤ m :=
      hRcomp _ _ _ (by simpa only [hb, hc, mul_one] using hTunit p a X Y hp ha hX hY)
    have hDZ11 : ‖T p a (R0 b' X Y) c‖ ≤ m :=
      hTcomp _ _ _ _ (by simpa only [hp, ha, hc, one_mul, mul_one] using hRunit b' X Y hb hX hY)
    have hDZ12 : ‖R0 a (T p b' X Y) c‖ ≤ m :=
      hRcomp _ _ _ (by simpa only [ha, hc, one_mul, mul_one] using hTunit p b' X Y hp hb hX hY)
    have hDZ13 : ‖T p a b' (R0 c X Y)‖ ≤ m :=
      hTcomp _ _ _ _ (by simpa only [hp, ha, hb, one_mul] using hRunit c X Y hc hX hY)
    have hDZ14 : ‖R0 a b' (T p c X Y)‖ ≤ m :=
      hRcomp _ _ _ (by simpa only [ha, hb, one_mul] using hTunit p c X Y hp hc hX hY)
    have hadd {u v : TangentSpace (𝓡 n) x} {s t : ℝ} (hu : ‖u‖ ≤ s) (hv : ‖v‖ ≤ t) :
        ‖u + v‖ ≤ s + t := (norm_add_le u v).trans (add_le_add hu hv)
    have hsub {u v : TangentSpace (𝓡 n) x} {s t : ℝ} (hu : ‖u‖ ≤ s) (hv : ‖v‖ ≤ t) :
        ‖u - v‖ ≤ s + t := (norm_sub_le u v).trans (add_le_add hu hv)
    have htwo {u : TangentSpace (𝓡 n) x} (hu : ‖u‖ ≤ m) : ‖(2 : ℝ) • u‖ ≤ 2 * m := by
      calc
        _ = 2 * ‖u‖ := by norm_num [norm_smul]
        _ ≤ 2 * m := mul_le_mul_of_nonneg_left hu (by norm_num)
    constructor
    · have h5 := hsub (hsub (hsub (hsub hCo1 hCo2) hCo3) hCo4) hCo5
      have h7 := hadd (hadd h5 hCo6) hCo7
      have h13 := hsub (hsub (hsub (hsub (hsub (hsub h7 hCo8) hCo9) hCo10)
        hCo11) hCo12) hCo13
      calc
        _ ≤ _ := h13
        _ = 13 * A0 * L0 := by dsimp only [m]; ring
    · have h2 := hadd hDZ1 hDZ2
      have h4 := hsub (hsub h2 (htwo hDZ3)) (htwo hDZ4)
      have h8 := hadd (hadd (hadd (hadd h4 (htwo hDZ5)) (htwo hDZ6)) hDZ7) hDZ8
      have h14 := hsub (hsub (hsub (hsub (hsub (hsub h8 hDZ9) hDZ10) hDZ11)
        hDZ12) hDZ13) hDZ14
      calc
        _ ≤ _ := h14
        _ = 18 * A0 * L0 := by dsimp only [m]; ring
  have hBunit (i j : ι) : ‖B0 (b i) (b j)‖ ≤ 3 * (n : ℝ) * L0 := by
    simpa only [b.norm_eq_one, mul_one] using hBn (b i) (b j)
  have hRcomp (u v w : TangentSpace (𝓡 n) x)
      (h : ‖u‖ * ‖v‖ * ‖w‖ ≤ 3 * (n : ℝ) * L0) :
      ‖R0 u v w‖ ≤ 3 * (n : ℝ) * A0 * L0 := by
    calc
      _ ≤ A0 * ‖u‖ * ‖v‖ * ‖w‖ := hRn u v w
      _ = A0 * (‖u‖ * ‖v‖ * ‖w‖) := by ring
      _ ≤ A0 * (3 * (n : ℝ) * L0) := mul_le_mul_of_nonneg_left h hA0
      _ = _ := by ring
  have hVnorm (γ : Fin 4 → ι) :
      ‖LV (fun r => b (γ r))‖ ≤ 43 * (n : ℝ) * A0 * L0 := by
    have hterm (r : ι) :
        ‖Co0 (b (γ 0)) (b r) (b r) (b (γ 1)) (b (γ 2)) (b (γ 3)) +
          DZ0 (b (γ 0)) (b (γ 1)) (b (γ 2)) (b (γ 3)) (b r) (b r)‖ ≤
        13 * A0 * L0 + 18 * A0 * L0 := by
      have hh := hpoly (b (γ 0)) (b r) (b r) (b (γ 1)) (b (γ 2)) (b (γ 3))
        (b.norm_eq_one _) (b.norm_eq_one _) (b.norm_eq_one _)
        (b.norm_eq_one _) (b.norm_eq_one _) (b.norm_eq_one _)
      exact (norm_add_le _ _).trans (add_le_add hh.1 hh.2)
    have hsum : ‖∑ r : ι,
        (Co0 (b (γ 0)) (b r) (b r) (b (γ 1)) (b (γ 2)) (b (γ 3)) +
          DZ0 (b (γ 0)) (b (γ 1)) (b (γ 2)) (b (γ 3)) (b r) (b r))‖ ≤
        31 * (n : ℝ) * A0 * L0 := by
      calc
        _ ≤ ∑ r : ι, ‖Co0 (b (γ 0)) (b r) (b r) (b (γ 1)) (b (γ 2)) (b (γ 3)) +
          DZ0 (b (γ 0)) (b (γ 1)) (b (γ 2)) (b (γ 3)) (b r) (b r)‖ := norm_sum_le _ _
        _ ≤ ∑ _r : ι, (13 * A0 * L0 + 18 * A0 * L0) :=
          Finset.sum_le_sum (fun r _ => hterm r)
        _ = _ := by simp only [Finset.sum_const, Finset.card_univ, hdim, nsmul_eq_mul]; ring
    have hru : ‖R0 (b (γ 1)) (b (γ 2)) (b (γ 3))‖ ≤ A0 := by
      simpa only [b.norm_eq_one, mul_one] using hRn (b (γ 1)) (b (γ 2)) (b (γ 3))
    have hBo : ‖B0 (b (γ 0)) (R0 (b (γ 1)) (b (γ 2)) (b (γ 3)))‖ ≤
        3 * (n : ℝ) * A0 * L0 := by
      calc
        _ ≤ 3 * (n : ℝ) * L0 * ‖R0 (b (γ 1)) (b (γ 2)) (b (γ 3))‖ := by
          simpa only [b.norm_eq_one, mul_one] using
            hBn (b (γ 0)) (R0 (b (γ 1)) (b (γ 2)) (b (γ 3)))
        _ ≤ 3 * (n : ℝ) * L0 * A0 :=
          mul_le_mul_of_nonneg_left hru (by positivity)
        _ = _ := by ring
    have hB1 : ‖R0 (B0 (b (γ 0)) (b (γ 1))) (b (γ 2)) (b (γ 3))‖ ≤
        3 * (n : ℝ) * A0 * L0 :=
      hRcomp _ _ _ (by simpa only [b.norm_eq_one, mul_one] using hBunit (γ 0) (γ 1))
    have hB2 : ‖R0 (b (γ 1)) (B0 (b (γ 0)) (b (γ 2))) (b (γ 3))‖ ≤
        3 * (n : ℝ) * A0 * L0 :=
      hRcomp _ _ _ (by simpa only [b.norm_eq_one, one_mul, mul_one] using hBunit (γ 0) (γ 2))
    have hB3 : ‖R0 (b (γ 1)) (b (γ 2)) (B0 (b (γ 0)) (b (γ 3)))‖ ≤
        3 * (n : ℝ) * A0 * L0 :=
      hRcomp _ _ _ (by simpa only [b.norm_eq_one, one_mul] using hBunit (γ 0) (γ 3))
    have hadd {u v : TangentSpace (𝓡 n) x} {s t : ℝ} (hu : ‖u‖ ≤ s) (hv : ‖v‖ ≤ t) :
        ‖u + v‖ ≤ s + t := (norm_add_le u v).trans (add_le_add hu hv)
    have hsub {u v : TangentSpace (𝓡 n) x} {s t : ℝ} (hu : ‖u‖ ≤ s) (hv : ‖v‖ ≤ t) :
        ‖u - v‖ ≤ s + t := (norm_sub_le u v).trans (add_le_add hu hv)
    calc
      _ ≤ _ := hsub (hsub (hsub (hadd hsum hBo) hB1) hB2) hB3
      _ = 43 * (n : ℝ) * A0 * L0 := by ring
  have hcard4 : (Fintype.card (Fin 4 → ι) : ℝ) = (n : ℝ) ^ 4 := by
    rw [Fintype.card_fun, hdim, Fintype.card_fin, Nat.cast_pow]
  have hsumSq : (∑ γ : Fin 4 → ι, ‖LT (fun r => b (γ r))‖) ^ 2 ≤
      (n : ℝ) ^ 4 * Q := by
    have hh := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 4 → ι))
      (fun _ => (1 : ℝ)) (fun γ => ‖LT (fun r => b (γ r))‖)
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hh
    rw [hcard4, ← hQnorm] at hh
    exact hh
  have hsumNorm : (∑ γ : Fin 4 → ι, ‖LT (fun r => b (γ r))‖) ≤ (n : ℝ) ^ 2 * L0 := by
    have hS0 : 0 ≤ ∑ γ : Fin 4 → ι, ‖LT (fun r => b (γ r))‖ :=
      Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    have hr0 : 0 ≤ (n : ℝ) ^ 2 * L0 := mul_nonneg (sq_nonneg _) hL0
    have hr : ((n : ℝ) ^ 2 * L0) ^ 2 = (n : ℝ) ^ 4 * Q := by rw [mul_pow, hLsq]; ring
    nlinarith only [hsumSq, hr, hS0, hr0]
  have hpairBound : pair z (k t) ≤ 43 * (n : ℝ) ^ 3 * A0 * Q := by
    calc
      _ = ∑ γ : Fin 4 → ι, g.inner x (LV (fun r => b (γ r)))
          (LT (fun r => b (γ r))) := hpairIntrinsic
      _ ≤ ∑ γ : Fin 4 → ι, ‖LV (fun r => b (γ r))‖ * ‖LT (fun r => b (γ r))‖ := by
        apply Finset.sum_le_sum
        intro γ _
        change inner ℝ (LV (fun r => b (γ r))) (LT (fun r => b (γ r))) ≤ _
        exact real_inner_le_norm _ _
      _ ≤ ∑ γ : Fin 4 → ι, (43 * (n : ℝ) * A0 * L0) * ‖LT (fun r => b (γ r))‖ :=
        Finset.sum_le_sum (fun γ _ => mul_le_mul_of_nonneg_right (hVnorm γ) (norm_nonneg _))
      _ = (43 * (n : ℝ) * A0 * L0) * ∑ γ : Fin 4 → ι, ‖LT (fun r => b (γ r))‖ :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ (43 * (n : ℝ) * A0 * L0) * ((n : ℝ) ^ 2 * L0) :=
        mul_le_mul_of_nonneg_left hsumNorm (by positivity)
      _ = 43 * (n : ℝ) ^ 3 * A0 * L0 ^ 2 := by ring
      _ = _ := by rw [hLsq]
  rw [hq]
  calc
    _ ≤ 2 * (43 * (n : ℝ) ^ 3 * A0 * Q) :=
      mul_le_mul_of_nonneg_left hpairBound (by norm_num)
    _ = _ := by ring

set_option maxHeartbeats 2400000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem ricciFlow_curvature_derivative_scalar_heat_le
    {I : Set ℝ} (F : RicciFlow n M I) {t : ℝ} (ht : t ∈ interior I)
    (x0 : M) {x : M}
    (hx : x ∈ (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)) x0).baseSet) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric 0).toRiemannianMetric⟩
    let V := EuclideanSpace ℝ (Fin n)
    let e := trivializationAt V (TangentSpace (𝓡 n)) x0
    let E := e.localFrame (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let G := fun (s : ℝ) (y : M) => ContinuousLinearMap.inCoordinates V
      (TangentSpace (𝓡 n)) (V →L[ℝ] ℝ)
      (fun z => TangentSpace (𝓡 n) z →L[ℝ] ℝ) x0 y x0 y ((F.metric s).inner y)
    let a := fun (s : ℝ) (y : M) (i j : Fin n) =>
      ((G s y).inverse (EuclideanSpace.proj j)) i
    let N := fun s (P Q : (y : M) → TangentSpace (𝓡 n) y) y =>
      (F.connection s).connection Q y (P y)
    let R := fun s (A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
      (F.connection s).curvatureOnFields A B C y
    let K := fun s (P A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
      N s P (R s A B C) y - R s (N s P A) B C y -
        R s A (N s P B) C y - R s A B (N s P C) y
    let H := fun (P Q A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
      N t P (K t Q A B C) y - K t (N t P Q) A B C y -
        K t Q (N t P A) B C y - K t Q A (N t P B) C y - K t Q A B (N t P C) y
    let W := fun s y (α β : Fin 4 → Fin n) => ∏ r, a s y (α r) (β r)
    let pair := fun s (y : M)
        (v w : (Fin 4 → Fin n) → TangentSpace (𝓡 n) y) =>
      ∑ α, ∑ β, W s y α β * (F.metric s).inner y (v α) (w β)
    let k := fun s (α : Fin 4 → Fin n) =>
      K s (E (α 0)) (E (α 1)) (E (α 2)) (E (α 3))
    let k1 := fun i (α : Fin 4 → Fin n) =>
      H (E i) (E (α 0)) (E (α 1)) (E (α 2)) (E (α 3))
    let q := fun s y => pair s y (fun α => k s α y) (fun α => k s α y)
    let d := fun (P : (y : M) → TangentSpace (𝓡 n) y) (f : M → ℝ) y =>
      mvfderiv (𝓡 n) f y (P y)
    let G2 := ∑ i, ∑ j, a t x i j *
      pair t x (fun α => k1 i α x) (fun α => k1 j α x)
    0 ≤ G2 ∧ deriv (fun s => q s x) t -
        (∑ i, ∑ j, a t x i j *
          (d (E i) (d (E j) (q t)) x - d (N t (E i) (E j)) (q t) x)) ≤
      -2 * G2 + 96 * ((n : ℝ) + 1) ^ 3 *
        (F.connection t).curvatureTensorNorm x * q t x := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric 0).toRiemannianMetric⟩
  let V := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt V (TangentSpace (𝓡 n)) x0
  let E := e.localFrame (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let G := fun (s : ℝ) (y : M) => ContinuousLinearMap.inCoordinates V
    (TangentSpace (𝓡 n)) (V →L[ℝ] ℝ)
    (fun z => TangentSpace (𝓡 n) z →L[ℝ] ℝ) x0 y x0 y ((F.metric s).inner y)
  let a := fun (s : ℝ) (y : M) (i j : Fin n) =>
    ((G s y).inverse (EuclideanSpace.proj j)) i
  let N := fun s (P Q : (y : M) → TangentSpace (𝓡 n) y) y =>
    (F.connection s).connection Q y (P y)
  let R := fun s (A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
    (F.connection s).curvatureOnFields A B C y
  let K := fun s (P A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
    N s P (R s A B C) y - R s (N s P A) B C y -
      R s A (N s P B) C y - R s A B (N s P C) y
  let H := fun (P Q A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
    N t P (K t Q A B C) y - K t (N t P Q) A B C y -
      K t Q (N t P A) B C y - K t Q A (N t P B) C y - K t Q A B (N t P C) y
  let J := fun (P Q A B C W : (y : M) → TangentSpace (𝓡 n) y) y =>
    N t P (H Q A B C W) y - H (N t P Q) A B C W y -
      H Q (N t P A) B C W y - H Q A (N t P B) C W y -
      H Q A B (N t P C) W y - H Q A B C (N t P W) y
  let W := fun s y (α β : Fin 4 → Fin n) => ∏ r, a s y (α r) (β r)
  let pair := fun s (y : M)
      (v w : (Fin 4 → Fin n) → TangentSpace (𝓡 n) y) =>
    ∑ α, ∑ β, W s y α β * (F.metric s).inner y (v α) (w β)
  let k := fun s (α : Fin 4 → Fin n) =>
    K s (E (α 0)) (E (α 1)) (E (α 2)) (E (α 3))
  let k1 := fun i (α : Fin 4 → Fin n) =>
    H (E i) (E (α 0)) (E (α 1)) (E (α 2)) (E (α 3))
  let k2 := fun i j (α : Fin 4 → Fin n) =>
    J (E i) (E j) (E (α 0)) (E (α 1)) (E (α 2)) (E (α 3))
  let q := fun s y => pair s y (fun α => k s α y) (fun α => k s α y)
  let d := fun (P : (y : M) → TangentSpace (𝓡 n) y) (f : M → ℝ) y =>
    mvfderiv (𝓡 n) f y (P y)
  let raised := fun i => e.symmL ℝ x ((G t x).inverse (EuclideanSpace.proj i))
  let dotk := fun α => deriv (fun s => k s α x) t
  let diff := fun α => ∑ i, ∑ j, a t x i j • k2 i j α x
  let G2 := ∑ i, ∑ j, a t x i j *
    pair t x (fun α => k1 i α x) (fun α => k1 j α x)
  let outputRate := ∑ α, ∑ β,
    W t x α β * (F.connection t).ricci x (k t α x) (k t β x)
  let inputRate := ∑ α, ∑ β, ∑ r : Fin 4,
    2 * (F.connection t).ricci x (raised (β r)) (raised (α r)) *
      (∏ s ∈ Finset.univ.erase r, a t x (α s) (β s)) *
        (F.metric t).inner x (k t α x) (k t β x)
  let A := (F.connection t).curvatureTensorNorm x
  have hid := ricciFlow_curvature_derivative_scalar_heat_identity F ht x0 hx
  change deriv (fun s => q s x) t -
      (∑ i, ∑ j, a t x i j *
        (d (E i) (d (E j) (q t)) x - d (N t (E i) (E j)) (q t) x)) =
    -2 * G2 + 2 * pair t x (fun α => dotk α - diff α) (fun α => k t α x) -
      2 * outputRate + inputRate at hid
  have hmetric := curvature_derivative_metric_rate_le (F.connection t) x0 hx
    (fun α => k t α x)
  change -2 * outputRate + inputRate ≤
    (2 * (n : ℝ) + 8 * (n : ℝ) ^ 2) * A * q t x at hmetric
  let g := F.metric t
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let cb := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let theta := e.localFrameCoeff (𝓡 n) cb
  let b := g.orthonormalBasis x
  let ι := Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))
  let coeff := fun (γ : Fin 4 → ι) (α : Fin 4 → Fin n) =>
    ∏ r, theta (α r) x (b (γ r))
  have htrace (i j : Fin n) :
      a t x i j = ∑ p, theta i x (b p) * theta j x (b p) :=
    metric_inverse_eq_sum_orthonormal_coordinates g x0 x hx i j
  have hweight (α β : Fin 4 → Fin n) :
      W t x α β = ∑ γ : Fin 4 → ι, coeff γ α * coeff γ β := by
    dsimp only [W]
    simp_rw [htrace]
    rw [Fintype.prod_sum]
    simp only [coeff, Finset.prod_mul_distrib]
    rfl
  have hgram {κ ρ : Type} [Fintype κ] [Fintype ρ]
      (c : ρ → κ → ℝ) (u v : κ → TangentSpace (𝓡 n) x) :
      (∑ i, ∑ j, (∑ p, c p i * c p j) * g.inner x (u i) (v j)) =
        ∑ p, g.inner x (∑ i, c p i • u i) (∑ j, c p j • v j) := by
    have hex (p : ρ) : g.inner x (∑ i, c p i • u i) (∑ j, c p j • v j) =
        ∑ i, ∑ j, (c p i * c p j) * g.inner x (u i) (v j) := by
      simp only [map_sum, map_smul, sum_apply, smul_apply,
        smul_eq_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [show (∑ p, g.inner x (∑ i, c p i • u i) (∑ j, c p j • v j)) =
      ∑ p, ∑ i, ∑ j, (c p i * c p j) * g.inner x (u i) (v j) from
        Finset.sum_congr rfl fun p _ => hex p]
    symm
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    exact (Finset.sum_mul ..).symm
  have hpair (u v : (Fin 4 → Fin n) → TangentSpace (𝓡 n) x) :
      pair t x u v = ∑ γ : Fin 4 → ι,
        g.inner x (∑ α, coeff γ α • u α) (∑ β, coeff γ β • v β) := by
    change (∑ α, ∑ β, W t x α β * g.inner x (u α) (v β)) = _
    simp_rw [hweight]
    exact hgram coeff u v
  have hq : 0 ≤ q t x := by
    change 0 ≤ pair t x (fun α => k t α x) (fun α => k t α x)
    rw [hpair]
    apply Finset.sum_nonneg
    intro γ _
    change 0 ≤ inner ℝ (∑ α, coeff γ α • k t α x) (∑ α, coeff γ α • k t α x)
    exact real_inner_self_nonneg
  let z := fun (γ : Fin 4 → ι) (i : Fin n) =>
    ∑ α, coeff γ α • k1 i α x
  have hG2 : G2 = ∑ γ : Fin 4 → ι, ∑ p : ι,
      g.inner x (∑ i, theta i x (b p) • z γ i)
        (∑ j, theta j x (b p) • z γ j) := by
    calc
      _ = ∑ i, ∑ j, a t x i j * ∑ γ : Fin 4 → ι,
          g.inner x (z γ i) (z γ j) := by
        dsimp only [G2]
        simp only [hpair, z]
      _ = ∑ γ : Fin 4 → ι, ∑ i, ∑ j,
          a t x i j * g.inner x (z γ i) (z γ j) := by
        simp only [Finset.mul_sum]
        calc
          _ = ∑ i, ∑ γ : Fin 4 → ι, ∑ j,
              a t x i j * g.inner x (z γ i) (z γ j) := by
            apply Finset.sum_congr rfl
            intro i _
            exact Finset.sum_comm
          _ = _ := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro γ _
        simp_rw [htrace]
        exact hgram (fun p i => theta i x (b p)) (z γ) (z γ)
  have hG2nonneg : 0 ≤ G2 := by
    rw [hG2]
    apply Finset.sum_nonneg
    intro γ _
    apply Finset.sum_nonneg
    intro p _
    change 0 ≤ inner ℝ (∑ i, theta i x (b p) • z γ i) (∑ i, theta i x (b p) • z γ i)
    exact real_inner_self_nonneg
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  have hcoeff : 86 * (n : ℝ) ^ 3 + 8 * (n : ℝ) ^ 2 + 2 * (n : ℝ) ≤
      96 * ((n : ℝ) + 1) ^ 3 := by
    nlinarith only [Nat.cast_nonneg (α := ℝ) n, sq_nonneg (n : ℝ),
      pow_nonneg (Nat.cast_nonneg (α := ℝ) n) 3]
  have hbound := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoeff hA) hq
  have hres := ricciFlow_curvature_derivative_reaction_pairing_le F ht x0 hx
  change 2 * pair t x (fun α => dotk α - diff α) (fun α => k t α x) ≤
    86 * (n : ℝ) ^ 3 * A * q t x at hres
  change 0 ≤ G2 ∧ deriv (fun s => q s x) t -
      (∑ i, ∑ j, a t x i j *
        (d (E i) (d (E j) (q t)) x - d (N t (E i) (E j)) (q t) x)) ≤
    -2 * G2 + 96 * ((n : ℝ) + 1) ^ 3 * A * q t x
  refine ⟨hG2nonneg, ?_⟩
  rw [hid]
  nlinarith only [hmetric, hres, hbound]

end PoincareConjecture.Proofs.M03
