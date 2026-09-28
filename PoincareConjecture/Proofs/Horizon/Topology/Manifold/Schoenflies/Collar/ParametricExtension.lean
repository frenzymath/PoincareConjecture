import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Collar.Extension









set_option autoImplicit false
set_option maxHeartbeats 800000

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NormedAddCommGroup F] [NormedSpace Real F]
  {n : Nat} [Fact (Module.finrank Real E = n + 1)]



theorem exists_contDiff_extension_sphere_family
    {T : Set Real} (hT : IsCompact T)
    (f : Real × sphere (0 : E) 1 -> F)
    (hf : ContMDiff (𝓘(Real, Real).prod (𝓡 n)) 𝓘(Real, F) ∞ f) :
    ∃ G : Real × E -> F, ContDiff Real ∞ G ∧
      ∀ t ∈ T, ∀ p : sphere (0 : E) 1, G (t, p) = f (t, p) := by
  classical
  let U : TopologicalSpace.Opens (Real × E) :=
    ⟨{q | q.2 ≠ 0}, isOpen_compl_singleton.preimage continuous_snd⟩
  let radial : U -> sphere (0 : E) 1 := fun q =>
    ⟨‖q.val.2‖⁻¹ • q.val.2, by simp [norm_smul, norm_ne_zero_iff.mpr q.property]⟩
  have hsp : ContMDiff ((𝓘(Real, Real)).prod (𝓘(Real, E))) 𝓘(Real, E) ∞
      (fun q : U => q.val.2) :=
    contMDiff_snd.comp contMDiff_subtype_val
  have hn : ContMDiff ((𝓘(Real, Real)).prod (𝓘(Real, E))) 𝓘(Real, Real) ∞
      (fun q : U => ‖q.val.2‖) := by
    intro q
    exact (contDiffAt_norm Real q.property).contMDiffAt.comp q (hsp q)
  have hr : ContMDiff ((𝓘(Real, Real)).prod (𝓘(Real, E))) (𝓡 n) ∞ radial :=
    ((hn.inv₀ (fun q => norm_ne_zero_iff.mpr q.property)).smul hsp).codRestrict_sphere _
  let g : Real × E -> F := fun q =>
    if hq : q.2 = 0 then 0 else f (q.1, radial ⟨q, hq⟩)
  have hg : ContDiffOn Real ∞ g U := by
    intro q hq
    have hs : ContMDiff ((𝓘(Real, Real)).prod (𝓘(Real, E))) 𝓘(Real, F) ∞
        (fun y : U => g y.val) := by
      convert hf.comp ((contMDiff_fst.comp contMDiff_subtype_val).prodMk hr) using 1
      funext y
      exact dif_neg y.property
    have hs' := contMDiffAt_subtype_iff.mp (hs ⟨q, hq⟩)
    rw [← modelWithCornersSelf_prod] at hs'
    rw [chartedSpaceSelf_prod] at hs'
    exact hs'.contDiffAt.contDiffWithinAt
  have hTU : T ×ˢ sphere (0 : E) 1 ⊆ U := fun q hq =>
    ne_zero_of_mem_unit_sphere ⟨q.2, hq.2⟩
  obtain ⟨G, V, hG, _, hTV, _, heq⟩ :=
    Poincare.Analysis.exists_contDiff_extension_near_compact
      (hT.prod (isCompact_sphere 0 1)) U.isOpen hTU g hg
  refine ⟨G, hG, ?_⟩
  intro t ht p
  rw [heq (hTV ⟨ht, p.property⟩)]
  have hp : p.val ≠ 0 := ne_zero_of_mem_unit_sphere p
  simp [g, hp, radial]



theorem exists_contDiff_compactlySupported_sphere_family
    {V : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    {T : Set Real} (hT : IsCompact T)
    (v : Real × sphere (0 : E) 1 -> V)
    (hv : ContMDiff ((𝓘(Real, Real)).prod (𝓡 n)) 𝓘(Real, V) ∞ v) :
    ∃ W : Real × E -> V, ContDiff Real ∞ W ∧ HasCompactSupport W ∧
      ∀ t ∈ T, ∀ p : sphere (0 : E) 1, W (t, p) = v (t, p) := by
  obtain ⟨G, hG, hGon⟩ := exists_contDiff_extension_sphere_family hT v hv
  let K : Set (Real × E) := T ×ˢ sphere (0 : E) 1
  have hK : IsCompact K := hT.prod (isCompact_sphere 0 1)
  obtain ⟨r, hr, hKr⟩ := hK.isBounded.subset_ball_lt 0 (0 : Real × E)
  let χ : ContDiffBump (0 : Real × E) := ⟨r, r + 1, hr, lt_add_one r⟩
  refine ⟨fun x => χ x • G x, χ.contDiff.smul hG,
    χ.hasCompactSupport.smul_right, ?_⟩
  intro t ht p
  change χ (t, p) • G (t, p) = v (t, p)
  rw [χ.one_of_mem_closedBall (ball_subset_closedBall (hKr ⟨ht, p.property⟩)),
    one_smul, hGon t ht p]

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1
private abbrev P3 := Real × E3
private instance : Fact (Module.finrank Real E3 = 2 + 1) := ⟨by simp⟩




theorem exists_contDiff_compactlySupported_velocity_extension
    {V : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
    {T : Set Real} (hT : IsCompact T) (G : P3 -> E3)
    (hG : ContDiff Real ∞ G)
    (v : Real × S2 -> V)
    (hv : ContMDiff ((𝓘(Real, Real)).prod (𝓡 2)) 𝓘(Real, V) ∞ v)
    {e : OpenPartialHomeomorph P3 P3}
    (he : T ×ˢ S2 ⊆ e.source)
    (himage : (fun z : P3 => (z.1, G z)) '' (T ×ˢ S2) ⊆ e.target)
    (hei : ContMDiffOn (𝓘(Real, P3)) (𝓘(Real, P3)) ∞ e.symm e.target)
    (hagree : ∀ t ∈ T, ∀ p : S2, e (t, p) = (t, G (t, p))) :
    ∃ W : P3 -> V, ContDiff Real ∞ W ∧ HasCompactSupport W ∧
      ∀ t ∈ T, ∀ p : S2, W (t, G (t, p)) = v (t, p) := by
  obtain ⟨v₀, hv₀, hv₀eq⟩ :=
    exists_contDiff_extension_sphere_family (E := E3) (F := V) (n := 2) hT v hv
  let K : Set P3 := (fun z : P3 => (z.1, G z)) '' (T ×ˢ S2)
  have hK : IsCompact K := by
    apply (hT.prod (isCompact_sphere 0 1)).image_of_continuousOn
    exact (continuous_fst.prodMk hG.continuous).continuousOn
  let u : P3 -> V := v₀ ∘ e.symm
  have hu : ContDiffOn Real ∞ u e.target := by
    intro z hz
    have hc := (hv₀.contMDiff (e.symm z)).comp z
      ((hei z hz).contMDiffAt (e.open_target.mem_nhds hz))
    change ContDiffWithinAt Real ∞ (v₀ ∘ e.symm) e.target z
    exact hc.contDiffAt.contDiffWithinAt
  obtain ⟨H, _, hH, _, hKH, _, heq⟩ :=
    Poincare.Analysis.exists_contDiff_extension_near_compact hK e.open_target himage u hu
  obtain ⟨r, hr, hKr⟩ := hK.isBounded.subset_ball_lt 0 (0 : P3)
  let χ : ContDiffBump (0 : P3) := ⟨r, r + 1, hr, lt_add_one r⟩
  refine ⟨fun x => χ x • H x, χ.contDiff.smul hH,
    χ.hasCompactSupport.smul_right, ?_⟩
  intro t ht p
  change χ (t, G (t, p)) • H (t, G (t, p)) = v (t, p)
  have hpoint : (t, G (t, p)) ∈ K :=
    ⟨(t, p), ⟨ht, p.property⟩, rfl⟩
  rw [χ.one_of_mem_closedBall (ball_subset_closedBall (hKr hpoint)), one_smul,
    heq (hKH hpoint)]
  have hsource : (t, (p : E3)) ∈ e.source := he ⟨ht, p.property⟩
  have hleft : e.symm (e (t, (p : E3))) = (t, (p : E3)) := e.left_inv hsource
  have himageEq : e (t, (p : E3)) = (t, G (t, p)) := hagree t ht p
  calc
    v₀ (e.symm (t, G (t, p))) = v₀ (e.symm (e (t, (p : E3)))) := by
      exact congrArg (fun x => v₀ (e.symm x)) himageEq.symm
    _ = v₀ (t, (p : E3)) := congrArg v₀ hleft
    _ = v (t, p) := hv₀eq t ht p

end Poincare.Manifold.Schoenflies
