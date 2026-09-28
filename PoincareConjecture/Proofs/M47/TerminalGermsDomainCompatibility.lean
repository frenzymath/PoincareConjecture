import PoincareConjecture.Proofs.M47.TerminalGermsOpenReadout
import PoincareConjecture.Proofs.M47.TerminalGermsFiniteDescent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace PoincareConjecture.M47

theorem terminalGerms_open_domains_metric_compatibility
    {n : ℕ} {ι : Type*} {P : ι → Type*} {N : Type*}
    [∀ i, TopologicalSpace (P i)] [TopologicalSpace N]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (P i)]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [∀ i, IsManifold (𝓡 n) ∞ (P i)] [IsManifold (𝓡 n) ∞ N]
    (q : ∀ i, P i → N)
    (hq : ∀ i, IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (q i))
    (V W : Opens N) (s : Finset ι)
    (hcover : ∀ y ∈ V, ∃ i ∈ s, ∃ x, q i x = y)
    (g : ∀ i, RiemannianMetric n (P i))
    (gV : RiemannianMetric n V) (gW : RiemannianMetric n W)
    (hV : ∀ i ∈ s, ∀ (x : P i) (hx : q i x ∈ V)
      (a b : TangentSpace (𝓡 n) x),
      (g i).inner x a b = gV.inner ⟨q i x, hx⟩
        (mfderiv (𝓡 n) (𝓡 n) (q i) x a) (mfderiv (𝓡 n) (𝓡 n) (q i) x b))
    (hW : ∀ i ∈ s, ∀ (x : P i) (hx : q i x ∈ W)
      (a b : TangentSpace (𝓡 n) x),
      (g i).inner x a b = gW.inner ⟨q i x, hx⟩
        (mfderiv (𝓡 n) (𝓡 n) (q i) x a) (mfderiv (𝓡 n) (𝓡 n) (q i) x b))
    (y : N) (hyV : y ∈ V) (hyW : y ∈ W)
    (v w : EuclideanSpace ℝ (Fin n)) :
    gV.inner ⟨y, hyV⟩ v w = gW.inner ⟨y, hyW⟩ v w := by
  obtain ⟨i, hi, x, hx⟩ := hcover y hyV
  have hxV : q i x ∈ V := by rw [hx]; exact hyV
  have hxW : q i x ∈ W := by rw [hx]; exact hyW
  let L := (hq i).mfderivToContinuousLinearEquiv (by simp) x
  let a := L.symm v
  let b := L.symm w
  have ha : mfderiv (𝓡 n) (𝓡 n) (q i) x a = v := L.apply_symm_apply _
  have hb : mfderiv (𝓡 n) (𝓡 n) (q i) x b = w := L.apply_symm_apply _
  have hV' : (g i).inner x a b = gV.inner ⟨y, hyV⟩ v w := by
    calc
      _ = gV.inner ⟨q i x, hxV⟩ _ _ := hV i hi x hxV a b
      _ = gV.inner ⟨y, hyV⟩ _ _ := congrArg
        (fun z : V => gV.inner z (mfderiv (𝓡 n) (𝓡 n) (q i) x a)
          (mfderiv (𝓡 n) (𝓡 n) (q i) x b)) (Subtype.ext hx)
      _ = _ := congrArg₂ (fun v w : EuclideanSpace ℝ (Fin n) =>
        gV.inner ⟨y, hyV⟩ v w) ha hb
  have hW' : (g i).inner x a b = gW.inner ⟨y, hyW⟩ v w := by
    calc
      _ = gW.inner ⟨q i x, hxW⟩ _ _ := hW i hi x hxW a b
      _ = gW.inner ⟨y, hyW⟩ _ _ := congrArg
        (fun z : W => gW.inner z (mfderiv (𝓡 n) (𝓡 n) (q i) x a)
          (mfderiv (𝓡 n) (𝓡 n) (q i) x b)) (Subtype.ext hx)
      _ = _ := congrArg₂ (fun v w : EuclideanSpace ℝ (Fin n) =>
        gW.inner ⟨y, hyW⟩ v w) ha hb
  exact hV'.symm.trans hW'

theorem terminalGerms_domain_flows_compatibility
    {n : ℕ} {ι : Type*} {P : ι → Type*} {N : Type*}
    [∀ i, TopologicalSpace (P i)] [TopologicalSpace N]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (P i)]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [∀ i, IsManifold (𝓡 n) ∞ (P i)] [IsManifold (𝓡 n) ∞ N]
    (tau : ι → ℝ) (F : ∀ i, RicciFlow n (P i) (Icc (-tau i) 0))
    (q : ∀ i, P i → N)
    (hq : ∀ i, IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (q i))
    (V W : Opens N) (s : Finset ι)
    (hcover : ∀ y ∈ V, ∃ i ∈ s, ∃ x, q i x = y)
    (deltaV deltaW : ℝ) (hdelta : ∀ i ∈ s, deltaV < tau i)
    (G : RicciFlow n V (Icc (-deltaV) 0))
    (H : RicciFlow n W (Icc (-deltaW) 0))
    (hG : ∀ t ∈ Icc (-deltaV) 0, ∀ i, t ∈ Icc (-tau i) 0 →
      ∀ (x : P i) (hx : q i x ∈ V) (a b : TangentSpace (𝓡 n) x),
      ((F i).metric t).inner x a b = (G.metric t).inner ⟨q i x, hx⟩
        (mfderiv (𝓡 n) (𝓡 n) (q i) x a) (mfderiv (𝓡 n) (𝓡 n) (q i) x b))
    (hH : ∀ t ∈ Icc (-deltaW) 0, ∀ i, t ∈ Icc (-tau i) 0 →
      ∀ (x : P i) (hx : q i x ∈ W) (a b : TangentSpace (𝓡 n) x),
      ((F i).metric t).inner x a b = (H.metric t).inner ⟨q i x, hx⟩
        (mfderiv (𝓡 n) (𝓡 n) (q i) x a) (mfderiv (𝓡 n) (𝓡 n) (q i) x b))
    (t : ℝ) (htV : t ∈ Icc (-deltaV) 0) (htW : t ∈ Icc (-deltaW) 0)
    (y : N) (hyV : y ∈ V) (hyW : y ∈ W)
    (v w : EuclideanSpace ℝ (Fin n)) :
    (G.metric t).inner ⟨y, hyV⟩ v w = (H.metric t).inner ⟨y, hyW⟩ v w := by
  have htau (i : ι) (hi : i ∈ s) : t ∈ Icc (-tau i) 0 :=
    ⟨(neg_le_neg (hdelta i hi).le).trans htV.1, htV.2⟩
  exact terminalGerms_open_domains_metric_compatibility q hq V W s hcover
    (fun i => (F i).metric t) (G.metric t) (H.metric t)
    (fun i hi => hG t htV i (htau i hi))
    (fun i hi => hH t htW i (htau i hi)) y hyV hyW v w

end PoincareConjecture.M47
