import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialRawPast
import PoincareConjecture.Proofs.M47.TerminalSourceRealization
import PoincareConjecture.Proofs.M47.CanonicalNeckCylinderMetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M47

theorem source_initial_past_slab_window
    {H M d b : ℝ} (hH : 0 < H) (hHM : H ≤ M) (hd : 0 < d) (hdM : d ≤ M)
    (hlong : -1 / 2 + b / H < -1 - 3 * d / (4 * M)) :
    let zeta := d / (8 * M)
    0 < zeta ∧ zeta ≤ 1 / 8 ∧
      -1 / 2 + b / H < -1 - 4 * zeta ∧
      ∀ s ∈ Icc (-(5 * zeta)) 0,
        H * (-1 + zeta + s + 1 / 2) ∈
          Icc b (H * (-1 + d / (4 * H) + 1 / 2)) := by
  let zeta := d / (8 * M)
  have hM : 0 < M := hH.trans_le hHM
  have hzeta : 0 < zeta := div_pos hd (by positivity)
  have hzetaSmall : zeta ≤ 1 / 8 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 8 * M)).mpr
    nlinarith only [hdM]
  have hlong' : -1 / 2 + b / H < -1 - 6 * zeta := by
    have heq : 3 * d / (4 * M) = 6 * zeta := by dsimp only [zeta]; ring
    rwa [heq] at hlong
  have hleft : -1 / 2 + b / H < -1 - 4 * zeta := by
    linarith only [hlong', hzeta]
  have hdiv : d / (4 * M) ≤ d / (4 * H) :=
    div_le_div_of_nonneg_left hd.le (by positivity)
      (mul_le_mul_of_nonneg_left hHM (by norm_num))
  have htwo : 2 * zeta = d / (4 * M) := by dsimp only [zeta]; ring
  have hanchor : zeta ≤ d / (4 * H) := by rw [← htwo] at hdiv; linarith only [hdiv, hzeta]
  refine ⟨hzeta, hzetaSmall, hleft, ?_⟩
  intro s hs
  constructor
  · have hdiv' : b / H ≤ -1 + zeta + s + 1 / 2 := by
      linarith only [hleft, hs.1]
    change b ≤ H * (-1 + zeta + s + 1 / 2)
    exact ((div_le_iff₀ hH).mp hdiv').trans_eq (mul_comm _ _)
  · apply mul_le_mul_of_nonneg_left _ hH.le
    linarith only [hanchor, hs.2]

theorem exists_source_initial_past_slab
    (P : M47Predecessors.{u}) {F : SurgeryFlowData.{u}}
    {C : GeneralizedSliceCarrier.{u}} {T q left zeta K : ℝ}
    (hzeta : 0 < zeta) (hzetaSmall : zeta ≤ 1 / 8)
    (hleft : left ≤ -1 - 4 * zeta)
    (U : TopologicalSpace.Opens C.carrier) (hne : (U : Set C.carrier).Nonempty)
    (D : SurgeryFlowCylinder F C T q (Icc left (-1 / 2)) U)
    (hcurv : ∀ v (hv : v ∈ Icc left (-1 / 2)),
      v ∈ Icc (-1 - 4 * zeta) (-1 + zeta) → ∀ x ∈ U,
        (F.connection (T + v / q)).curvatureTensorNorm (D.forward v hv x) ≤ K * q) :
    let raw := fun s : ℝ => -1 + zeta + s
    ∃ hmem : MapsTo raw (Icc (-(5 * zeta)) 0) (Icc left (-1 / 2)),
      ∃ G : RicciFlow 3 U (Icc (-(5 * zeta)) 0),
        (∀ s (hs : s ∈ Icc (-(5 * zeta)) 0) (x : U),
          (∀ v w : TangentSpace (𝓡 3) x,
            (G.metric s).inner x v w = D.pullbackInner (raw s) (hmem hs) x.val
              (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x v)
              (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x w)) ∧
          (G.connection s).scalarCurvature x =
            (F.connection (T + raw s / q)).scalarCurvature
              (D.forward (raw s) (hmem hs) x.val) / q ∧
          (G.connection s).curvatureTensorNorm x =
            (F.connection (T + raw s / q)).curvatureTensorNorm
              (D.forward (raw s) (hmem hs) x.val) / q) ∧
        ∀ s ∈ Icc (-(5 * zeta)) 0, ∀ x : U, (G.connection s).curvatureTensorNorm x ≤ K := by
  let raw := fun s : ℝ => -1 + zeta + s
  have hraw : MapsTo raw (Icc (-(5 * zeta)) 0) (Icc (-1 - 4 * zeta) (-1 + zeta)) := by
    intro s hs
    dsimp only [raw]
    constructor <;> linarith only [hs.1, hs.2]
  have hmem : MapsTo raw (Icc (-(5 * zeta)) 0) (Icc left (-1 / 2)) := by
    intro s hs
    have hr := hraw hs
    exact ⟨hleft.trans hr.1, by linarith only [hr.2, hzetaSmall]⟩
  have hmono : StrictMono raw := by
    intro s t hst
    dsimp only [raw]
    linarith only [hst]
  have hclock : ∀ s ∈ Icc (-(5 * zeta)) 0,
      (T + (-1 + zeta) / q) + s / q = T + raw s / q := by
    intro s _hs
    dsimp only [raw]
    ring
  let e := Proofs.M47.seedCylinderReclock D D.scale_pos ordConnected_Icc
    raw hmem (hmono.strictMonoOn _) hclock
  have htau : 0 < 5 * zeta := by positivity
  obtain ⟨G, hread⟩ := terminalSourceRealization_surgery P htau U hne e
  have hfunctions (s : ℝ) (hs : s ∈ Icc (-(5 * zeta)) 0) :
      (⟨(T + (-1 + zeta) / q) + s / q, fun y : U => e.forward s hs y.val⟩ :
        (t : ℝ) × (U → (F.slice t).carrier)) =
          ⟨T + raw s / q, fun y : U => D.forward (raw s) (hmem hs) y.val⟩ := by
    apply Sigma.ext (hclock s hs)
    apply Function.hfunext rfl
    intro y y' hyy
    cases hyy
    exact Proofs.M47.seedCylinderReclock_forward_heq D D.scale_pos ordConnected_Icc
      raw hmem (hmono.strictMonoOn _) hclock s hs y.val
  have hfinal (s : ℝ) (hs : s ∈ Icc (-(5 * zeta)) 0) (x : U) :
      (∀ v w : TangentSpace (𝓡 3) x,
        (G.metric s).inner x v w = D.pullbackInner (raw s) (hmem hs) x.val
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x v)
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x w)) ∧
      (G.connection s).scalarCurvature x =
        (F.connection (T + raw s / q)).scalarCurvature
          (D.forward (raw s) (hmem hs) x.val) / q ∧
      (G.connection s).curvatureTensorNorm x =
        (F.connection (T + raw s / q)).curvatureTensorNorm
          (D.forward (raw s) (hmem hs) x.val) / q := by
    refine ⟨?_, ?_, ?_⟩
    · intro v w
      rw [(hread s hs x).1 v w,
        Proofs.M47.neck_reclock_pullbackInner D D.scale_pos ordConnected_Icc
          raw hmem (hmono.strictMonoOn _) hclock s hs]
      rw [div_self D.scale_pos.ne', one_mul]
    · have hr := congrArg (fun p : (t : ℝ) × (U → (F.slice t).carrier) =>
        (F.connection p.1).scalarCurvature (p.2 x) / q) (hfunctions s hs)
      exact (hread s hs x).2.1.trans hr
    · have hr := congrArg (fun p : (t : ℝ) × (U → (F.slice t).carrier) =>
        (F.connection p.1).curvatureTensorNorm (p.2 x) / q) (hfunctions s hs)
      exact (hread s hs x).2.2.trans hr
  refine ⟨hmem, G, hfinal, ?_⟩
  intro s hs x
  rw [(hfinal s hs x).2.2]
  exact (div_le_iff₀ D.scale_pos).mpr (hcurv (raw s) (hmem hs) (hraw hs) x.val x.property)

end PoincareConjecture.M47
