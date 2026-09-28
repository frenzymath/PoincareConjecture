import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Positivity.Global
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.TimeTranslation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Matrix
open scoped Manifold ContDiff Bundle BigOperators Topology

universe u

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J K : Set ℝ}

def SmoothExhaustion.translate {F : RicciFlow n M J} {O : M}
    (S : SmoothExhaustion F O) (c : ℝ)
    (hKJ : (fun t : ℝ => t + c) '' K ⊆ J) (hK : K.OrdConnected) (hne : K.Nontrivial) :
    SmoothExhaustion (F.translate c hKJ hK hne) O where
  toFun := S.toFun
  smooth := S.smooth
  bound := S.bound
  bound_nonneg := S.bound_nonneg
  distance_lower t ht := S.distance_lower (t + c) (hKJ ⟨t, ht, rfl⟩)
  distance_upper t ht := S.distance_upper (t + c) (hKJ ⟨t, ht, rfl⟩)
  gradient_bound t ht := S.gradient_bound (t + c) (hKJ ⟨t, ht, rfl⟩)
  hessian_bound t ht := S.hessian_bound (t + c) (hKJ ⟨t, ht, rfl⟩)

end PoincareConjecture.RicciFlow

namespace Poincare.RicciFlow.Harnack

open PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

lemma hamiltonBlockPos_translate {a b a' b' : ℝ} (F : RicciFlow n M (Ioo a b))
    (c : ℝ) (hKJ : (fun t : ℝ => t + c) '' Ioo a' b' ⊆ Ioo a b)
    (hK : (Ioo a' b').OrdConnected) (hne : (Ioo a' b').Nontrivial)
    (t : ℝ) (x : M) (τ : ℝ) :
    HamiltonBlockPos (F.translate c hKJ hK hne) t x τ ↔
      HamiltonBlockPos F (t + c) x τ := Iff.rfl

theorem hamiltonBlockPos_on_open_set_of_smoothExhaustion_time_origin [T2Space M]
    (hC : RicciFlowCurvatureTheory.{u}) {a b c T : ℝ}
    (F : RicciFlow n M (Ioo a b)) (O : M) (S : RicciFlow.SmoothExhaustion F O)
    (V : Set M) (hV : IsOpen V)
    (hproper : ∀ r : ℝ, IsCompact {x | S.toFun x ≤ r ∧ x ∈ V})
    (hcT : c < T) (hJ : Ioc c T ⊆ Ioo a b) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ∈ Ioc c T, ∀ x ∈ V, ∀ j ≤ 2,
      (F.connection t).curvatureDerivativeNorm j x ≤ K)
    (hcurv : ∀ t ∈ Ioc c T, ∀ x ∈ V, (F.connection t).NonnegativeCurvatureOperator x) :
    ∀ t ∈ Ioc c T, ∀ x ∈ V, HamiltonBlockPos F t x (t - c) := by
  have hmap : (fun s : ℝ => s + c) '' Ioo (a - c) (b - c) ⊆ Ioo a b := by
    rintro _ ⟨s, hs, rfl⟩
    constructor <;> linarith [hs.1, hs.2]
  have hne : (Ioo (a - c) (b - c)).Nontrivial := by
    obtain ⟨s, hs, r, hr, hsr⟩ := F.nontrivial
    refine ⟨s - c, ⟨by linarith [hs.1], by linarith [hs.2]⟩,
      r - c, ⟨by linarith [hr.1], by linarith [hr.2]⟩, ?_⟩
    intro h
    apply hsr
    linarith
  let G := F.translate c hmap ordConnected_Ioo hne
  let S' := S.translate c hmap ordConnected_Ioo hne
  have hshift {s : ℝ} (hs : s ∈ Ioc 0 (T - c)) : s + c ∈ Ioc c T := by
    constructor <;> linarith [hs.1, hs.2]
  have hJ' : Ioc 0 (T - c) ⊆ Ioo (a - c) (b - c) := by
    intro s hs
    have hm := hJ (hshift hs)
    constructor <;> linarith [hm.1, hm.2]
  have hp := hamiltonBlockPos_on_open_set_of_smoothExhaustion hC G O S' V hV hproper
    (sub_pos.mpr hcT) hJ' hK
    (fun s hs => hbound (s + c) (hshift hs))
    (fun s hs => hcurv (s + c) (hshift hs))
  intro t ht x hx
  have htime : t - c ∈ Ioc 0 (T - c) := ⟨sub_pos.mpr ht.1, sub_le_sub_right ht.2 c⟩
  have h := hp (t - c) htime x hx
  rw [hamiltonBlockPos_translate] at h
  simpa only [sub_add_cancel] using h

theorem hamiltonBlockPos_of_smoothExhaustion_time_origin [T2Space M]
    (hC : RicciFlowCurvatureTheory.{u}) {a b c T : ℝ}
    (F : RicciFlow n M (Ioo a b)) (O : M) (S : RicciFlow.SmoothExhaustion F O)
    (hproper : ∀ r : ℝ, IsCompact {x | S.toFun x ≤ r})
    (hcT : c < T) (hJ : Ioc c T ⊆ Ioo a b) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ∈ Ioc c T, ∀ x, ∀ j ≤ 2,
      (F.connection t).curvatureDerivativeNorm j x ≤ K)
    (hcurv : ∀ t ∈ Ioc c T, ∀ x, (F.connection t).NonnegativeCurvatureOperator x) :
    ∀ t ∈ Ioc c T, ∀ x, HamiltonBlockPos F t x (t - c) := by
  intro t ht x
  apply hamiltonBlockPos_on_open_set_of_smoothExhaustion_time_origin hC F O S
    univ isOpen_univ (by simpa only [mem_univ, and_true] using hproper) hcT hJ hK
    (fun s hs y _ => hbound s hs y) (fun s hs y _ => hcurv s hs y) t ht x (mem_univ x)

private lemma posSemidef_of_tendsto_entries {ι κ : Type*} [Fintype ι]
    {l : Filter κ} [l.NeBot] {A : κ → Matrix ι ι ℝ} {B : Matrix ι ι ℝ}
    (hlim : ∀ i j, Tendsto (fun q => A q i j) l (𝓝 (B i j)))
    (hpos : ∀ᶠ q in l, (A q).PosSemidef) : B.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.ext
    intro i j
    simp only [star_trivial]
    apply tendsto_nhds_unique_of_eventuallyEq (hlim j i) (hlim i j)
    filter_upwards [hpos] with q hq
    simpa only [star_trivial] using hq.1.apply i j
  · intro v
    have hquad : Tendsto (fun q => star v ⬝ᵥ (A q *ᵥ v)) l
        (𝓝 (star v ⬝ᵥ (B *ᵥ v))) := by
      simp only [dotProduct, Matrix.mulVec]
      apply tendsto_finsetSum
      intro i _
      apply tendsto_const_nhds.mul
      apply tendsto_finsetSum
      intro j _
      exact (hlim i j).mul_const (v j)
    exact ge_of_tendsto hquad (hpos.mono fun q hq => hq.dotProduct_mulVec_nonneg v)

theorem hamiltonBlockPos_of_tendsto_elapsedTime {a b : ℝ}
    (F : RicciFlow n M (Ioo a b)) (t : ℝ) (x : M)
    {ι : Type*} {l : Filter ι} [l.NeBot] {f : ι → ℝ} {τ : ℝ}
    (hf : Tendsto f l (𝓝 τ)) (hτ : τ ≠ 0)
    (hpos : ∀ᶠ q in l, HamiltonBlockPos F t x (f q)) :
    HamiltonBlockPos F t x τ := by
  let e := (F.metric t).orthonormalBasis x
  let Q (r : ℝ) := Matrix.fromBlocks
    (fun ac bd : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) ×
        Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) =>
      (F.connection t).curvatureTensor x (e ac.1) (e ac.2) (e bd.1) (e bd.2))
    (fun ac d => hamiltonP (F.connection t) x (e ac.1) (e ac.2) (e d))
    (fun c bd => hamiltonP (F.connection t) x (e bd.1) (e bd.2) (e c))
    (fun a b => hamiltonM (F.connection t) r x (e a) (e b))
  change (Q τ).PosSemidef
  apply posSemidef_of_tendsto_entries (A := fun q => Q (f q)) _ hpos
  intro i j
  have hentry : ContinuousAt (fun r => Q r i j) τ := by
    rcases i with ac | a <;> rcases j with bd | b
    · exact continuousAt_const
    · exact continuousAt_const
    · exact continuousAt_const
    · change ContinuousAt (fun r : ℝ => _ + _ / (2 * r)) τ
      exact continuousAt_const.add (continuousAt_const.div
        (continuousAt_const.mul continuousAt_id) (mul_ne_zero two_ne_zero hτ))
  exact hentry.tendsto.comp hf

theorem hamiltonBlockPos_of_time_origin_limit {T₀ T₁ a : ℝ}
    (F : RicciFlow n M (Ioo T₀ T₁)) (t : ℝ) (x : M) (hat : a < t)
    (hpos : ∀ c ∈ Ioo a t, HamiltonBlockPos F t x (t - c)) :
    HamiltonBlockPos F t x (t - a) := by
  apply hamiltonBlockPos_of_tendsto_elapsedTime F t x
    ((continuousAt_const.sub continuousAt_id).tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] a ≤ 𝓝 a)) (sub_pos.mpr hat).ne'
  filter_upwards [Ioo_mem_nhdsGT hat] with c hc
  exact hpos c hc

end Poincare.RicciFlow.Harnack
