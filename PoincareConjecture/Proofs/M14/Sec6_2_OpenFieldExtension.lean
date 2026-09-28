import PoincareConjecture.Proofs.M14.Mathlib.PullbackSectionSmooth
import PoincareConjecture.Proofs.M14.Sec6_2_ProductExtension
import Mathlib.Geometry.Manifold.PartitionOfUnity

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {γ : ℝ → G.Point} {J : Set ℝ} {Y : ∀ s, G.Horizontal (γ s)}

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in

theorem exists_pullbackExtension_of_isOpen (hJ : IsOpen J)
    (hY : ContMDiffOn (𝓘(ℝ, ℝ))
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun s => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
        (E := G.Horizontal) (γ s) (Y s)) J) :
    Nonempty (M14PullbackExtension G γ J Y) := by
  classical
  let : LocallyCompactSpace (EuclideanHalfSpace 1) := by
    change LocallyCompactSpace {v : EuclideanSpace ℝ (Fin 1) // 0 ≤ v 0}
    have hc : Continuous (fun v : EuclideanSpace ℝ (Fin 1) => v 0) := by
      fun_prop
    exact (isClosed_le continuous_const hc).locallyCompactSpace
  let : LocallyCompactSpace
      (ModelProd (EuclideanHalfSpace 1) (EuclideanSpace ℝ (Fin n))) :=
    inferInstanceAs (LocallyCompactSpace
      (EuclideanHalfSpace 1 × EuclideanSpace ℝ (Fin n)))
  let : LocallyCompactSpace G.Point := ChartedSpace.locallyCompactSpace
    (ModelProd (EuclideanHalfSpace 1) (EuclideanSpace ℝ (Fin n))) G.Point
  let D : TopologicalSpace.Opens (ℝ × G.Point) := ⟨J ×ˢ Set.univ, hJ.prod isOpen_univ⟩
  let : LocallyCompactSpace D := D.isOpen.locallyCompactSpace
  let f : ContMDiffMap ((𝓘(ℝ, ℝ)).prod (spacetimeModel n))
      (spacetimeModel n) D G.Point ∞ :=
    ⟨fun z => z.val.2, contMDiff_snd.comp contMDiff_subtype_val⟩
  let : ∀ z, AddCommGroup (((f : D → G.Point) *ᵖ G.Horizontal) z) :=
    fun z => inferInstanceAs (AddCommGroup (G.Horizontal (f z)))
  have hfst : ContMDiff ((𝓘(ℝ, ℝ)).prod (spacetimeModel n)) (𝓘(ℝ, ℝ)) ∞
      (fun z : D => z.val.1) := contMDiff_fst.comp contMDiff_subtype_val
  have hYD := hY.comp_contMDiff hfst (fun z => z.property.1)
  have hγ := (FiberBundle.continuous_proj
    (EuclideanSpace ℝ (Fin n)) G.Horizontal).comp_continuousOn hY.continuousOn
  have hγD : Continuous (fun z : D => γ z.val.1) :=
    hγ.comp_continuous hfst.continuous (fun z => z.property.1)
  let A : Set D := {z | γ z.val.1 = z.val.2}
  have hA : IsClosed A := isClosed_eq hγD f.contMDiff.continuous
  let t (z : D) : Set (((f : D → G.Point) *ᵖ G.Horizontal) z) :=
    {v | ∀ h : γ z.val.1 = z.val.2, v = (h ▸ Y z.val.1 : G.Horizontal z.val.2)}
  have ht (z : D) : Convex ℝ (t z) := by
    intro v hv w hw a b _ _ hab h
    rw [hv h, hw h, ← add_smul, hab, one_smul]
  have hlocal (z : D) : ∃ U ∈ 𝓝 z,
      ∃ v : ∀ w, ((f : D → G.Point) *ᵖ G.Horizontal) w,
        ContMDiffOn ((𝓘(ℝ, ℝ)).prod (spacetimeModel n))
          (((𝓘(ℝ, ℝ)).prod (spacetimeModel n)).prod
            𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
          (fun w => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) w (v w)) U ∧
        ∀ w ∈ U, v w ∈ t w := by
    by_cases hz : z ∈ A
    · let e := trivializationAt (EuclideanSpace ℝ (Fin n)) G.Horizontal (γ z.val.1)
      let U : Set D := {w | γ w.val.1 ∈ e.baseSet ∧ w.val.2 ∈ e.baseSet}
      have hU : IsOpen U :=
        (e.open_baseSet.preimage hγD).inter
          (e.open_baseSet.preimage f.contMDiff.continuous)
      have hp : γ z.val.1 ∈ e.baseSet :=
        mem_baseSet_trivializationAt (EuclideanSpace ℝ (Fin n)) G.Horizontal _
      have hzU : z ∈ U := ⟨hp, hz ▸ hp⟩
      let y : D → EuclideanSpace ℝ (Fin n) := fun w =>
        (e (Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
          (E := G.Horizontal) (γ w.val.1) (Y w.val.1))).2
      have hpair := e.contMDiffOn.comp hYD.contMDiffOn
        (fun w (hw : w ∈ U) => e.mem_source.mpr hw.1)
      have hy : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (spacetimeModel n))
          (𝓡 n) ∞ y U := fun w hw => (hpair w hw).snd
      have hmap := f.contMDiff.contMDiffOn.prodMk hy
      have hs := (e.contMDiffOn_symm.comp hmap
        (fun w (hw : w ∈ U) => e.mem_target.mpr hw.2)).congr
          (fun w hw => e.mk_symm hw.2 (y w))
      refine ⟨U, hU.mem_nhds hzU, (fun w => e.symm (f w) (y w)), ?_, ?_⟩
      · intro w hw
        exact (Bundle.contMDiffWithinAt_pullback_section_iff f
          (fun w => e.symm (f w) (y w)) U w).mpr (hs w hw)
      · intro w hw h
        rcases w with ⟨⟨r, q⟩, hr⟩
        change γ r = q at h
        subst q
        exact e.symm_apply_apply_mk hw.1 (Y r)
    · refine ⟨Aᶜ, hA.isOpen_compl.mem_nhds hz, (fun _ => 0),
        (Bundle.contMDiff_zeroSection ℝ _).contMDiffOn, ?_⟩
      intro w hw h
      exact (hw h).elim
  obtain ⟨V, hV⟩ := exists_contMDiffSection_forall_mem_convex_of_local
    ((𝓘(ℝ, ℝ)).prod (spacetimeModel n))
    (F_fiber := EuclideanSpace ℝ (Fin n))
    ((f : D → G.Point) *ᵖ G.Horizontal) t ht hlocal
  have hVs : ContMDiff ((𝓘(ℝ, ℝ)).prod (spacetimeModel n))
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun z : D => Bundle.TotalSpace.mk'
        (EuclideanSpace ℝ (Fin n)) (E := G.Horizontal) z.val.2 (V z)) := by
    intro z
    apply contMDiffWithinAt_univ.mp
    exact (Bundle.contMDiffWithinAt_pullback_section_iff f V Set.univ z).mp
      (V.contMDiff z).contMDiffWithinAt
  let W : ℝ → HorizontalSection G.spacetime := fun r p =>
    if hr : r ∈ J then V ⟨(r, p), ⟨hr, Set.mem_univ p⟩⟩ else 0
  have hW_eq (w : D) : W w.val.1 w.val.2 = V w := by
    dsimp only [W]
    rw [dif_pos w.property.1]
  have hW : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (spacetimeModel n))
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun z : ℝ × G.Point => Bundle.TotalSpace.mk'
        (EuclideanSpace ℝ (Fin n)) (E := G.Horizontal) z.2 (W z.1 z.2))
      (J ×ˢ Set.univ) := by
    intro z hz
    have hh : ContMDiffAt ((𝓘(ℝ, ℝ)).prod (spacetimeModel n))
        ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
        (fun w : D => Bundle.TotalSpace.mk'
          (EuclideanSpace ℝ (Fin n)) (E := G.Horizontal) w.val.2
            (W w.val.1 w.val.2)) ⟨z, hz⟩ := by
      simpa only [hW_eq] using hVs ⟨z, hz⟩
    exact ((contMDiffAt_subtype_iff (U := D)
      (f := fun z : ℝ × G.Point => Bundle.TotalSpace.mk'
        (EuclideanSpace ℝ (Fin n)) (E := G.Horizontal) z.2 (W z.1 z.2))).mp
          hh).contMDiffWithinAt
  refine ⟨{
    extension := W
    domain := Set.univ
    domain_open := isOpen_univ
    graph_mem := fun _ _ => Set.mem_univ _
    spatial_smooth := ?_
    joint_smooth := ⟨J ×ˢ Set.univ, hJ.prod isOpen_univ,
      fun s hs => ⟨hs, Set.mem_univ _⟩, hW⟩
    agrees := ?_
    parameter_derivative := ?_ }⟩
  · intro r
    by_cases hr : r ∈ J
    · intro p _
      have hh := (hW (r, p) ⟨hr, Set.mem_univ _⟩).contMDiffAt
        ((hJ.prod isOpen_univ).mem_nhds ⟨hr, Set.mem_univ _⟩)
      exact (hh.comp p (contMDiffAt_const.prodMk contMDiffAt_id)).contMDiffWithinAt
    · have hw0 : W r = (fun _ => 0) := by
        funext p
        exact dif_neg hr
      rw [hw0]
      exact (Bundle.contMDiff_zeroSection ℝ G.spacetime.Horizontal).contMDiffOn
  · intro s hs
    dsimp only [W]
    rw [dif_pos hs]
    exact hV ⟨(s, γ s), ⟨hs, Set.mem_univ _⟩⟩ rfl
  · intro s hs
    exact horizontal_parameter_hasDerivAt_of_contMDiffAt W s (γ s)
      ((hW (s, γ s) ⟨hs, Set.mem_univ _⟩).contMDiffAt
        ((hJ.prod isOpen_univ).mem_nhds ⟨hs, Set.mem_univ _⟩))

end PoincareConjecture.M14
