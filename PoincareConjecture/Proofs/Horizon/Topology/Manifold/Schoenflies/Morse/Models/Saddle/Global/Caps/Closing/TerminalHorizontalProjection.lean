import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.ModelDomain
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Collar.ProjectionChart
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Circle.CollarDifferential

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1

theorem exists_circle_height_projection
    {h : E2 → Real} {V : Set E2} (hV : IsOpen V)
    (hVs : sphere (0 : E2) 1 ⊆ V) (hh : ContDiffOn Real ∞ h V)
    (c : Real) (hc : ∀ x ∈ sphere (0 : E2) 1, h x = c)
    (hreg : ∀ x ∈ sphere (0 : E2) 1, fderiv Real h x ≠ 0) :
    ∃ T : PartialDiffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
      sphere (0 : E2) 1 ⊆ T.source ∧ T.source ⊆ V ∧
      (∀ x ∈ sphere (0 : E2) 1, T x = x) ∧
      T '' sphere (0 : E2) 1 = sphere (0 : E2) 1 ∧
      ∀ x ∈ T.source, 0 < 1 + h x - c ∧
        T x = ((1 + h x - c) / ‖x‖) • x ∧ h x = c + ‖T x‖ - 1 := by
  let W := V ∩ {x : E2 | x ≠ 0 ∧ 0 < 1 + h x - c}
  have hW : IsOpen W := by
    have ho : IsOpen (V ∩ {x : E2 | 0 < 1 + h x - c}) :=
      ((contDiffOn_const.add hh).sub contDiffOn_const).continuousOn.isOpen_inter_preimage
        hV isOpen_Ioi
    convert ho.inter isClosed_singleton.isOpen_compl using 1
    ext x
    simp only [W, mem_inter_iff, mem_ofPred_eq, mem_compl_iff, mem_singleton_iff]
    tauto
  have hsW : sphere (0 : E2) 1 ⊆ W := by
    intro x hx
    refine ⟨hVs hx, ?_, ?_⟩
    · exact ne_zero_of_mem_unit_sphere ⟨x, hx⟩
    · rw [hc x hx]
      norm_num
  let k : E2 → E2 := fun x => ((1 + h x - c) / ‖x‖) • x
  have hk : ContDiffOn Real ∞ k W := by
    intro x hx
    exact ((((contDiffAt_const.add ((hh x hx.1).contDiffAt (hV.mem_nhds hx.1))).sub
      contDiffAt_const).div (contDiffAt_norm Real hx.2.1)
        (norm_ne_zero_iff.mpr hx.2.1)).smul contDiffAt_id).contDiffWithinAt
  have hkfix (x : E2) (hx : x ∈ sphere (0 : E2) 1) : k x = x := by
    simp only [k, hc x hx, mem_sphere_zero_iff_norm.mp hx]
    simp
  have hknorm (x : E2) (hx : x ∈ W) : ‖k x‖ = 1 + h x - c := by
    dsimp only [k]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hx.2.2 (norm_pos_iff.mpr hx.2.1))]
    exact div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hx.2.1)
  obtain ⟨k₀, hk₀, _, hk₀eq⟩ := Poincare.Parabolic.Interior.exists_compact_smooth_extension
    (isCompact_sphere (0 : E2) 1) hW hsW hk
  have hk₀fix (q : S1) : k₀ q = q := (hk₀eq q q.property).eq_of_nhds.trans (hkfix q q.property)
  have hk₀der (q : S1) : Bijective (fderiv Real k₀ q) := by
    let D := fderiv Real k₀ q
    let L := fderiv Real h q
    have hqd : DifferentiableAt Real h q :=
      ((hh q (hVs q.property)).contDiffAt (hV.mem_nhds (hVs q.property))).differentiableAt (by simp)
    have hnorm : (fun x => ‖k₀ x‖ ^ 2) =ᶠ[𝓝 (q : E2)] fun x => (1 + h x - c) ^ 2 := by
      filter_upwards [hk₀eq q q.property, hW.mem_nhds (hsW q.property)] with x he hx
      rw [he, hknorm x hx]
    have hdleft := (hk₀.differentiable (by simp) q).hasFDerivAt.norm_sq
    have hdright := (((hasFDerivAt_const (1 : Real) (q : E2)).add hqd.hasFDerivAt).sub_const c).pow 2
    simp only [Pi.add_apply] at hdright
    have hder := hnorm.fderiv_eq (𝕜 := Real)
    rw [hdleft.fderiv, hdright.fderiv, hk₀fix q, hc q q.property] at hder
    have hinner (u : E2) : inner Real (q : E2) (D u) = L u := by
      have heq := congrArg (fun A : E2 →L[Real] Real => A u) hder
      norm_num at heq
      exact heq
    have htan (u : E2) (hu : inner Real (q : E2) u = 0) : D u = u :=
      fderiv_eq_self_on_circle_tangent hk₀ hk₀fix q u hu
    have hpp : inner Real (q : E2) q = 1 := by simp
    have hproj (u : E2) : inner Real (q : E2) (u - inner Real (q : E2) u • (q : E2)) = 0 := by
      simp only [inner_sub_right, inner_smul_right, hpp, mul_one, sub_self]
    have hLp : L q ≠ 0 := by
      intro hp
      apply hreg q q.property
      ext u
      change L u = 0
      have hzero : L (u - inner Real (q : E2) u • (q : E2)) = 0 := by
        rw [← hinner, htan _ (hproj u)]
        exact hproj u
      simpa only [map_sub, map_smul, hp, smul_zero, sub_zero] using hzero
    have hinj : Injective D := by
      apply LinearMap.ker_eq_bot.mp
      apply LinearMap.ker_eq_bot'.mpr
      intro u hu
      change D u = 0 at hu
      have hDu : D u = u - inner Real (q : E2) u • (q : E2) +
          inner Real (q : E2) u • D q := by
        have heq := htan _ (hproj u)
        rw [map_sub, map_smul] at heq
        exact eq_add_of_sub_eq heq
      have heq := congrArg (inner Real (q : E2)) hu
      rw [hDu] at heq
      simp only [inner_add_right, hproj, inner_smul_right, hinner, zero_add,
        inner_zero_right] at heq
      have hqu : inner Real (q : E2) u = 0 := (mul_eq_zero.mp heq).resolve_right hLp
      rwa [htan u hqu] at hu
    exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩
  have hlocal (q : E2) (hq : q ∈ sphere (0 : E2) 1) :
      IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ k q :=
    (localDiffeomorphAt_of_smooth_bijective_derivative hk₀ (hk₀der ⟨q, hq⟩)).congr_of_eventuallyEq
      (hk₀eq q hq).symm
  obtain ⟨n, hn, _, hnk, hns, hnsi⟩ := Poincare.exists_openPartialHomeomorph_of_injOn_compact
    (isCompact_sphere (0 : E2) 1)
    (show InjOn k (sphere (0 : E2) 1) by
      intro x hx y hy heq
      rwa [hkfix x hx, hkfix y hy] at heq) hlocal
  let T : PartialDiffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞ :=
    { n.restrOpen W hW with
      contMDiffOn_toFun := hns.mono inter_subset_left
      contMDiffOn_invFun := hnsi.mono inter_subset_left }
  have hTc : sphere (0 : E2) 1 ⊆ T.source := fun x hx => ⟨hn hx, hsW hx⟩
  have hTfix (x : E2) (hx : x ∈ sphere (0 : E2) 1) : T x = x :=
    (hnk (hn hx)).trans (hkfix x hx)
  refine ⟨T, hTc, fun x hx => hx.2.1, hTfix, ?_, ?_⟩
  · rw [image_congr hTfix, image_id']
  · intro x hx
    have heq : T x = k x := hnk hx.1
    refine ⟨hx.2.2.2, heq, ?_⟩
    rw [heq, hknorm x hx.2]
    ring

open SaddleLevel

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

theorem exists_terminal_model_height_projection
    (data : TerminalSaddleData M P p e) (i : Fin 3) :
    ∃ c : Real, (c = data.ends.lowerCut ∨ c = data.ends.upperCut) ∧
      ∃ T : PartialDiffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        sphere (0 : E2) 1 ⊆ T.source ∧ T.source ⊆ (data.modelDisk i).source ∧
        (∀ x ∈ sphere (0 : E2) 1, T x = x) ∧
        T '' sphere (0 : E2) 1 = sphere (0 : E2) 1 ∧
        ∀ x ∈ T.source,
          inner Real (M.v : E3)
            (data.toTerminalSaddleGeometry.filledModel (data.modelDisk i x)) =
              c + ‖T x‖ - 1 := by
  let h : S2 → Real := fun q => inner Real (M.v : E3)
    (data.toTerminalSaddleGeometry.filledModel q)
  have hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h :=
    (innerSL Real (M.v : E3)).contMDiff.comp
      (data.toTerminalSaddleGeometry.filledModel.contMDiff.comp contMDiff_coe_sphere)
  obtain ⟨c, hc, hboundary⟩ : ∃ c : Real,
      (c = data.ends.lowerCut ∨ c = data.ends.upperCut) ∧
      ∀ x ∈ sphere (0 : E2) 1, h (data.modelDisk i x) = c := by
    rcases terminal_model_domain_boundary data i with ⟨_, hlo⟩ | ⟨_, hhi⟩
    · exact ⟨data.ends.lowerCut, Or.inl rfl, hlo⟩
    · exact ⟨data.ends.upperCut, Or.inr rfl, hhi⟩
  have hsm : ContDiffOn Real ∞ (h ∘ data.modelDisk i) (data.modelDisk i).source :=
    (hh.comp_contMDiffOn (data.modelDisk_smooth i)).contDiffOn
  have hregular (x : E2) (hx : x ∈ sphere (0 : E2) 1) :
      fderiv Real (h ∘ data.modelDisk i) x ≠ 0 := by
    let m : PartialDiffeomorph (𝓡 2) (𝓡 2) E2 S2 ∞ :=
      { data.modelDisk i with
        contMDiffOn_toFun := data.modelDisk_smooth i
        contMDiffOn_invFun := data.modelDisk_symm_smooth i }
    have hmx := m.isLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞
      (data.modelDisk_source i (sphere_subset_closedBall hx))
    have hreg := terminal_model_cut_regular data (data.modelDisk i x)
      (hc.imp (fun he => (hboundary x hx).trans he) (fun he => (hboundary x hx).trans he))
    change mfderiv (𝓡 2) 𝓘(Real, Real) h (m x) ≠ 0 at hreg
    intro hz
    have hchain := mfderiv_comp x (hh.mdifferentiable (by simp) _)
      (hmx.mdifferentiableAt (by simp))
    change mfderiv (𝓡 2) 𝓘(Real, Real) (h ∘ (m : E2 → S2)) x = _ at hchain
    have hz' : mfderiv (𝓡 2) 𝓘(Real, Real) (h ∘ (m : E2 → S2)) x = 0 := by
      simpa only [mfderiv_eq_fderiv, TangentSpace, m,
        OpenPartialHomeomorph.coe_toPartialEquiv] using hz
    rw [hz'] at hchain
    apply hreg
    ext u
    obtain ⟨w, rfl⟩ := (hmx.mfderivToContinuousLinearEquiv (by simp)).surjective u
    have heq := congrArg (fun A : E2 →L[Real] Real => A w) hchain
    exact heq.symm
  obtain ⟨T, hTs, hTV, hTfix, hTc, hTh⟩ := exists_circle_height_projection
    (data.modelDisk i).open_source
    (sphere_subset_closedBall.trans (data.modelDisk_source i)) hsm c hboundary hregular
  exact ⟨c, hc, T, hTs, hTV, hTfix, hTc, fun x hx => (hTh x hx).2.2⟩

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing
