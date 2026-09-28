import PoincareConjecture.Proofs.M47.TerminalSourceRealization
import PoincareConjecture.Proofs.M47.CanonicalNeckCylinderMetric
import PoincareConjecture.Proofs.M47.CanonicalNeckOpenSource











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

open Proofs.M47

private theorem recentBased_zero_metric
    {F : SurgeryFlowData.{u}} {T q : ℝ} {J : Set ℝ} {V : Set (F.slice T).carrier}
    (e : SurgeryFlowCylinder F (F.slice T) T q J V)
    (U : TopologicalSpace.Opens (F.slice T).carrier) (hUV : (U : Set _) ⊆ V)
    (hz : (0 : ℝ) ∈ J) (hbased : ∀ x ∈ V, HEq (e.forward 0 hz x) x)
    (x : U) (v w : TangentSpace (𝓡 3) x) :
    e.pullbackInner 0 hz x.val
      (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → (F.slice T).carrier) x v)
      (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → (F.slice T).carrier) x w) =
      q * (F.metric T).inner x.val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → (F.slice T).carrier) x v)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → (F.slice T).carrier) x w) := by
  have hfunctions : (⟨T + 0 / q, fun y : U => e.forward 0 hz y.val⟩ :
      (t : ℝ) × (U → (F.slice t).carrier)) = ⟨T, Subtype.val⟩ := by
    apply Sigma.ext (by simp only [zero_div, add_zero])
    apply Function.hfunext rfl
    intro y y' hyy
    cases hyy
    exact hbased y.val (hUV y.property)
  have hm := congrArg (fun p : (t : ℝ) × (U → (F.slice t).carrier) =>
    q * (F.metric p.1).inner (p.2 x)
      (mfderiv (𝓡 3) (𝓡 3) p.2 x v) (mfderiv (𝓡 3) (𝓡 3) p.2 x w)) hfunctions
  have he := ((e.forward_smooth 0 hz).mono hUV).contMDiffAt (U.isOpen.mem_nhds x.property)
  have hd := mfderiv_comp x (he.mdifferentiableAt (by simp))
    (contMDiff_subtype_val (n := ∞) x |>.mdifferentiableAt (by simp))
  change mfderiv (𝓡 3) (𝓡 3) (fun y : U => e.forward 0 hz y.val) x = _ at hd
  rw [hd] at hm
  exact hm




theorem exists_source_initial_recent_ordinary
    (P : M47Predecessors.{u}) {F : SurgeryFlowData.{u}}
    {T q Q s : ℝ} {J : Set ℝ} {V : Set (F.slice T).carrier}
    (e : SurgeryFlowCylinder F (F.slice T) T q J V)
    (hQ : 0 < Q) (hs : 0 < s) (hJ : Icc (0 : ℝ) s ⊆ J)
    (hbased : ∀ hz x, x ∈ V → HEq (e.forward 0 hz x) x)
    (U : TopologicalSpace.Opens (F.slice T).carrier) (hUV : (U : Set _) ⊆ V)
    (center : U)
    (hscalar : (F.connection (T + s / q)).scalarCurvature
      (e.forward s (hJ ⟨hs.le, le_rfl⟩) center.val) = Q) :
    let H := Q / q
    ∃ htimes : MapsTo (fun u : ℝ => s + u / H) (Icc (-(H * s)) 0) J,
    ∃ recent : SurgeryFlowCylinder F (F.slice T) (T + s / q) Q (Icc (-(H * s)) 0) U,
    ∃ G : RicciFlow 3 U (Icc (-(H * s)) 0),
      (∀ u (hu : u ∈ Icc (-(H * s)) 0) x,
        (⟨(T + s / q) + u / Q, recent.forward u hu x⟩ : Σ t, (F.slice t).carrier) =
          ⟨T + (s + u / H) / q, e.forward (s + u / H) (htimes hu) x⟩) ∧
      (∀ u (hu : u ∈ Icc (-(H * s)) 0) (x : U) (v w : TangentSpace (𝓡 3) x),
        (G.metric u).inner x v w = H * e.pullbackInner (s + u / H) (htimes hu) x.val
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → (F.slice T).carrier) x v)
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → (F.slice T).carrier) x w)) ∧
      (G.connection 0).scalarCurvature center = 1 ∧
      ∀ (x : U) (v w : TangentSpace (𝓡 3) x),
        (G.metric (-(H * s))).inner x v w = Q * (F.metric T).inner x.val
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → (F.slice T).carrier) x v)
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → (F.slice T).carrier) x w) := by
  let H := Q / q
  have hq : 0 < q := e.scale_pos
  have hH : 0 < H := div_pos hQ hq
  have hdr : 0 < H * s := mul_pos hH hs
  let phi := fun u : ℝ => s + u / H
  have htimes : MapsTo phi (Icc (-(H * s)) 0) J := by
    intro u hu
    apply hJ
    have hlo : -s ≤ u / H := (le_div_iff₀ hH).mpr (by nlinarith only [hu.1])
    have hhi : u / H ≤ 0 := div_nonpos_of_nonpos_of_nonneg hu.2 hH.le
    constructor <;> dsimp only [phi] <;> linarith only [hlo, hhi]
  have hmono : StrictMonoOn phi (Icc (-(H * s)) 0) := by
    intro u _ v _ huv
    have h := (div_lt_div_iff_of_pos_right hH).mpr huv
    change s + u / H < s + v / H
    linarith only [h]
  have hclock : ∀ u ∈ Icc (-(H * s)) 0,
      (T + s / q) + u / Q = T + phi u / q := by
    intro u _
    dsimp only [phi, H]
    field_simp
    ring
  let raw := seedCylinderReclock e hQ ordConnected_Icc phi htimes hmono hclock
  let recent := raw.restrict Subset.rfl ordConnected_Icc hUV
  obtain ⟨G, hG⟩ := terminalSourceRealization_surgery P hdr U ⟨center.val, center.property⟩ recent
  have hmaps (u : ℝ) (hu : u ∈ Icc (-(H * s)) 0) (x : (F.slice T).carrier) :
      (⟨(T + s / q) + u / Q, recent.forward u hu x⟩ : Σ t, (F.slice t).carrier) =
        ⟨T + phi u / q, e.forward (phi u) (htimes hu) x⟩ := by
    apply Sigma.ext (hclock u hu)
    exact seedCylinderReclock_forward_heq e hQ ordConnected_Icc phi htimes hmono hclock u hu x
  have hmetric (u : ℝ) (hu : u ∈ Icc (-(H * s)) 0)
      (x : U) (v w : TangentSpace (𝓡 3) x) :
      (G.metric u).inner x v w = H * e.pullbackInner (phi u) (htimes hu) x.val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → (F.slice T).carrier) x v)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → (F.slice T).carrier) x w) := by
    rw [(hG u hu x).1 v w]
    exact neck_reclock_pullbackInner e hQ ordConnected_Icc phi htimes hmono hclock u hu _ _ _
  refine ⟨htimes, recent, G, hmaps, hmetric, ?_, ?_⟩
  · have hz : (0 : ℝ) ∈ Icc (-(H * s)) 0 := ⟨by linarith only [hdr], le_rfl⟩
    have hsame (r : ℝ) (hr : r ∈ J) (hrs : r = s) :
        HEq (e.forward r hr center.val) (e.forward s (hJ ⟨hs.le, le_rfl⟩) center.val) := by
      subst r
      rfl
    have hp : (⟨(T + s / q) + 0 / Q, recent.forward 0 hz center.val⟩ :
        Σ t, (F.slice t).carrier) =
        ⟨T + s / q, e.forward s (hJ ⟨hs.le, le_rfl⟩) center.val⟩ := by
      apply Sigma.ext (by simp only [zero_div, add_zero])
      exact (seedCylinderReclock_forward_heq e hQ ordConnected_Icc phi htimes hmono hclock
        0 hz center.val).trans (hsame _ _ (by simp only [phi, zero_div, add_zero]))
    have hr := congrArg (fun p : Σ t, (F.slice t).carrier =>
      (F.connection p.1).scalarCurvature p.2) hp
    rw [(hG 0 hz center).2.1, hr, hscalar, div_self hQ.ne']
  · intro x v w
    have hb : -(H * s) ∈ Icc (-(H * s)) 0 := ⟨le_rfl, by linarith only [hdr]⟩
    have hphi : s + (-(H * s)) / H = 0 := by
      field_simp
      ring
    have hzeroRead (r : ℝ) (hr : r ∈ J) (hr0 : r = 0) :
        e.pullbackInner r hr x.val
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → (F.slice T).carrier) x v)
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → (F.slice T).carrier) x w) =
        q * (F.metric T).inner x.val
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → (F.slice T).carrier) x v)
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → (F.slice T).carrier) x w) := by
      subst r
      exact recentBased_zero_metric e U hUV _ (hbased _) x v w
    rw [hmetric (-(H * s)) hb x v w, hzeroRead _ _ hphi]
    dsimp only [H]
    field_simp

end PoincareConjecture.M47
