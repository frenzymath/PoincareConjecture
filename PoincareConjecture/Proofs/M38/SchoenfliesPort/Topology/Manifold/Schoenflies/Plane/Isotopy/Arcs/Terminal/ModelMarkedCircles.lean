import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.ModelCircles
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.StandardCriticalLevel
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Planar.Pairing
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Resolution.Strips.Components







open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.Poincare.Manifold.Schoenflies.PlaneArcs
open _root_.Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
open _root_.PoincareConjecture

namespace M38Schoenflies



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

open SaddleLevel _root_.Poincare.Geometry.Manifold

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1
local notation "IR2" => 𝓘(Real, Real × Real)

private theorem whole_band_exterior_strips
    {h : S2 → Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    {p : S2} (hunique : ∀ q, h q = h p →
      mfderiv (𝓡 2) 𝓘(Real, Real) h q = 0 → q = p)
    (hconnected : IsPreconnected (h ⁻¹' {h p}))
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (hform : ∀ x ∈ e.source, h (e x) = h p - x 0 ^ 2 + x 1 ^ 2)
    {r ε : Real} (hr : 0 < r) (hrs : closedSquare r ⊆ e.source) (hε : 0 < ε) :
    ∃ (a b a₀ b₀ : Fin 2 → Real) (η : Real)
        (F : Fin 2 → OpenPartialHomeomorph (Real × Real) S2),
      0 < η ∧ η < ε ∧
      (∀ i, a i < a₀ i ∧ a₀ i < b₀ i ∧ b₀ i < b i) ∧
      (∀ i, Icc (a i) (b i) ×ˢ Icc (-η) η ⊆ (F i).source) ∧
      (∀ i z, z ∈ (F i).source → h (F i z) = h p + z.2) ∧
      Pairwise (fun i j => Disjoint (F i).target (F j).target) ∧
      (⋃ i, F i '' (Icc (a₀ i) (b₀ i) ×ˢ ({0} : Set Real))) =
        (h ⁻¹' {h p}) \ e '' openSquare r ∧
      (∀ i, range (fun j : Fin 2 × Fin 2 => e (contact r j)) ∩
        (F i '' (Icc (a₀ i) (b₀ i) ×ˢ ({0} : Set Real))) =
          {F i (a₀ i, 0), F i (b₀ i, 0)}) ∧
      h ⁻¹' Icc (h p - η) (h p + η) ⊆ e '' openSquare r ∪
        ⋃ i, F i '' (Icc (a i) (b i) ×ˢ Icc (-η) η) := by
  have hcomponent : connectedComponentIn (h ⁻¹' {h p}) p = h ⁻¹' {h p} :=
    hconnected.connectedComponentIn rfl
  obtain ⟨a₀, b₀, w, F, hw, hab, hFs, _, _, hheight, hcentral, hdisj, hends, _⟩ :=
    exists_disjoint_actual_exterior_strips hh hunique e he0 hep he hei hform hr hrs
  change _ = connectedComponentIn (h ⁻¹' {h p}) p \ _ at hcentral
  rw [hcomponent] at hcentral
  let a : Fin 2 → Real := fun i => a₀ i - w / 2
  let b : Fin 2 → Real := fun i => b₀ i + w / 2
  let V : Fin 2 → Set (Real × Real) :=
    fun i => Ioo (a i) (b i) ×ˢ Ioo (-w / 2) (w / 2)
  have hVsub (i : Fin 2) : V i ⊆ (F i).source := by
    intro z hz
    rw [hFs i]
    dsimp [V, a, b] at hz
    exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩,
      ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩⟩
  have hVopen (i : Fin 2) : IsOpen (F i '' V i) :=
    (F i).isOpen_image_of_subset_source (isOpen_Ioo.prod isOpen_Ioo) (hVsub i)
  let O : Set S2 := e '' openSquare r ∪ ⋃ i, F i '' V i
  have hO : IsOpen O :=
    (e.isOpen_image_of_subset_source (isOpen_openSquare r)
      ((openSquare_subset_closedSquare r).trans hrs)).union (isOpen_iUnion hVopen)
  have hfiber : h ⁻¹' {h p} ⊆ O := by
    intro q hq
    by_cases hqp : q ∈ e '' openSquare r
    · exact Or.inl hqp
    · right
      obtain ⟨i, z, hz, heq⟩ := mem_iUnion.mp (hcentral.superset ⟨hq, hqp⟩)
      have ht : z.2 = 0 := hz.2
      refine mem_iUnion_of_mem i ⟨z, ?_, heq⟩
      dsimp [V, a, b]
      exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩,
        ⟨by linarith, by linarith⟩⟩
  obtain ⟨δ, hδ, hcover⟩ :=
    Poincare.Topology.exists_closedBand_subset_of_fiber_subset_open hh.continuous hO hfiber
  let η : Real := min δ (min (w / 2) ε) / 2
  have hη : 0 < η := half_pos (lt_min hδ (lt_min (half_pos hw) hε))
  have hηδ : η ≤ δ :=
    (half_le_self (le_min hδ.le (le_min (half_pos hw).le hε.le))).trans (min_le_left _ _)
  have hηw : η < w / 2 :=
    (half_lt_self (lt_min hδ (lt_min (half_pos hw) hε))).trans_le
      ((min_le_right _ _).trans (min_le_left _ _))
  have hηε : η < ε :=
    (half_lt_self (lt_min hδ (lt_min (half_pos hw) hε))).trans_le
      ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨a, b, a₀, b₀, η, F, hη, hηε, ?_, ?_, hheight, hdisj, hcentral, hends, ?_⟩
  · intro i
    exact ⟨by dsimp [a]; linarith, hab i, by dsimp [b]; linarith⟩
  · intro i z hz
    rw [hFs i]
    dsimp [a, b] at hz
    exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩,
      ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩⟩
  · intro q hq
    have hqO : q ∈ O := hcover ⟨by linarith [hq.1], by linarith [hq.2]⟩
    rcases hqO with hqp | hqs
    · exact Or.inl hqp
    · right
      obtain ⟨i, z, hz, rfl⟩ := mem_iUnion.mp hqs
      have hzheight := hheight i z (hVsub i hz)
      refine mem_iUnion_of_mem i ⟨z, ?_, rfl⟩
      exact ⟨⟨hz.1.1.le, hz.1.2.le⟩,
        ⟨by linarith [hq.1], by linarith [hq.2]⟩⟩

private theorem source_circles_of_two_components
    {h : S2 → Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    {c : Real} (hreg : ∀ q, h q = c → mfderiv (𝓡 2) 𝓘(Real, Real) h q ≠ 0)
    (hcard : Nat.card (ConnectedComponents (h ⁻¹' {c})) = 2)
    (D Q : Fin 2 → Set S2) (q : Fin 2 → S2)
    (hq : ∀ i, q i ∈ Q i) (hQD : ∀ i, Q i ⊆ D i)
    (hD : ∀ i x, x ∈ D i → connectedComponentIn (h ⁻¹' {c}) x = D i)
    (hdis : Pairwise (fun i j => Disjoint (D i) (D j))) :
    ∃ γ : Fin 2 → S1 → S2,
      (∀ i, ContMDiff (𝓡 1) (𝓡 2) ∞ (γ i)) ∧
      Injective (fun x : Fin 2 × S1 => γ x.1 x.2) ∧
      (∀ i x, Injective (mfderiv (𝓡 1) (𝓡 2) (γ i) x)) ∧
      (⋃ i, range (γ i)) = h ⁻¹' {c} ∧ ∀ i, Q i ⊆ range (γ i) := by
  classical
  have hqD (i : Fin 2) := hQD i (hq i)
  have hqL (i : Fin 2) : q i ∈ h ⁻¹' {c} := by
    have hm : q i ∈ connectedComponentIn (h ⁻¹' {c}) (q i) := by
      rw [hD i _ (hqD i)]
      exact hqD i
    exact connectedComponentIn_subset _ _ hm
  choose γ hγ hi hd hγrange using fun i =>
    exists_smooth_circle_regularLevelComponent hh c hreg (q i) (hqL i)
  have hrange (i : Fin 2) : range (γ i) = D i := (hγrange i).trans (hD i _ (hqD i))
  have hjoint : Injective (fun x : Fin 2 × S1 => γ x.1 x.2) := by
    rintro ⟨i, x⟩ ⟨j, y⟩ heq
    have hij : i = j := by
      by_contra hn
      exact disjoint_left.mp (hdis hn) ((hrange i).subset (mem_range_self x))
        ((hrange j).subset ⟨y, heq.symm⟩)
    subst j
    exact Prod.ext rfl (hi i heq)
  let J (i : Fin 2) : ConnectedComponents (h ⁻¹' {c}) :=
    ConnectedComponents.mk ⟨q i, hqL i⟩
  have hJi : Injective J := by
    intro i j hij
    have hm := (Poincare.Topology.connectedComponents_eq_iff_mem
      (⟨q i, hqL i⟩ : h ⁻¹' {c}) ⟨q j, hqL j⟩).mp hij
    change q i ∈ connectedComponentIn (h ⁻¹' {c}) (q j) at hm
    rw [hD j _ (hqD j)] at hm
    by_contra hn
    exact disjoint_left.mp (hdis hn) (hqD i) hm
  have : Finite (ConnectedComponents (h ⁻¹' {c})) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; decide)
  have hJs : Surjective J :=
    ((Nat.bijective_iff_injective_and_card J).mpr ⟨hJi, by simp [hcard]⟩).2
  refine ⟨γ, hγ, hjoint, hd, ?_, fun i => (hQD i).trans (hrange i).superset⟩
  apply Subset.antisymm
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    rw [hγrange i] at hi
    exact connectedComponentIn_subset _ _ hi
  · intro x hx
    obtain ⟨i, hi⟩ := hJs (ConnectedComponents.mk ⟨x, hx⟩)
    apply mem_iUnion_of_mem i
    rw [hγrange i]
    exact (Poincare.Topology.connectedComponents_eq_iff_mem
      (⟨x, hx⟩ : h ⁻¹' {c}) ⟨q i, hqL i⟩).mp hi.symm

private theorem negative_branch_source_circles
    (F : S2 → E3) (hF : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ F)
    (v : E3) (hv : ‖v‖ = 1) (p : S2)
    (hunique : ∀ q, inner Real v (F q) = inner Real v (F p) →
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (F q)) q = 0 → q = p)
    (hconnected : IsPreconnected {q : S2 | inner Real v (F q) = inner Real v (F p)})
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (hform : ∀ x ∈ e.source, inner Real v (F (e x)) =
      inner Real v (F p) - x 0 ^ 2 + x 1 ^ 2)
    {ε : Real} (hε : 0 < ε)
    (hreg : ∀ t ∈ Ioc (0 : Real) ε, ∀ q,
      inner Real v (F q) = inner Real v (F p) - t →
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (F q)) q ≠ 0)
    (hnot : ∀ t ∈ Ioc (0 : Real) ε,
      ¬ IsPreconnected {q : S2 | inner Real v (F q) = inner Real v (F p) - t}) :
    ∃ r δ : Real, 0 < r ∧ closedSquare r ⊆ e.source ∧
      0 < δ ∧ δ < ε ∧ δ < r ^ 2 ∧
      ∀ t ∈ Ioc (0 : Real) δ,
        ∃ γ : Fin 2 → S1 → S2,
          (∀ i, ContMDiff (𝓡 1) (𝓡 2) ∞ (γ i)) ∧
          Injective (fun x : Fin 2 × S1 => γ x.1 x.2) ∧
          (∀ i x, Injective (mfderiv (𝓡 1) (𝓡 2) (γ i) x)) ∧
          (⋃ i, range (γ i)) = {q : S2 | inner Real v (F q) = inner Real v (F p) - t} ∧
          ∀ i, negativePatchArc e r t i ⊆ range (γ i) := by
  let h (q : S2) := inner Real v (F q)
  have hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h :=
    (innerSL Real v).contMDiff.comp hF.contMDiff
  obtain ⟨r, hr, _, hrs, hpair⟩ :=
    exists_exterior_adjacent_pairing hF hv p hunique e he0 hep he hei hform hε
  have hcomponent : connectedComponentIn (h ⁻¹' {h p}) p = h ⁻¹' {h p} :=
    hconnected.connectedComponentIn rfl
  change (∀ i j : Fin 2 × Fin 2, e (contact r i) ∈ connectedComponentIn
    (connectedComponentIn (h ⁻¹' {h p}) p \ e '' openSquare r) (e (contact r j)) ↔ i.1 = j.1) ∨
    (∀ i j : Fin 2 × Fin 2, e (contact r i) ∈ connectedComponentIn
    (connectedComponentIn (h ⁻¹' {h p}) p \ e '' openSquare r) (e (contact r j)) ↔ i.2 = j.2) at hpair
  rw [hcomponent] at hpair
  obtain ⟨a, b, a₀, b₀, η, G, hη, hηε, hchain, hrect, hheight, hdis, hcentral, hends, hband⟩ :=
    whole_band_exterior_strips hh hunique hconnected e he0 hep he hei hform hr hrs hε
  obtain ⟨δ, hδ, hδη, hδr, hresolve⟩ := exists_resolved_level_components e hr hrs hform
    G a b a₀ b₀ hη hchain hrect hheight hdis hcentral hends hband hpair
  have hδε := hδη.trans hηε
  refine ⟨r, δ, hr, hrs, hδ, hδε, hδr, ?_⟩
  intro t ht
  have htε : t ∈ Ioc (0 : Real) ε := ⟨ht.1, ht.2.trans hδε.le⟩
  have hdata : Nat.card (ConnectedComponents (h ⁻¹' {h p - t})) = 2 ∧
      ∃ D : Fin 2 → Set S2, Pairwise (fun i j => Disjoint (D i) (D j)) ∧
        (∀ i, negativePatchArc e r t i ⊆ D i) ∧
        ∀ i q, q ∈ D i → connectedComponentIn (h ⁻¹' {h p - t}) q = D i := by
    rcases hresolve with hneg | hpos
    · exact (hneg t ht.1 ht.2).2
    · exact False.elim (hnot t htε (hpos t ht.1 ht.2).1.isPreconnected)
  obtain ⟨hcard, D, hDdis, hpatch, hD⟩ := hdata
  have hz : 0 ∈ Icc (-hyperbolaRadius r t) (hyperbolaRadius r t) :=
    ⟨neg_nonpos.mpr (hyperbolaRadius_pos (ht.2.trans_lt hδr)).le,
      (hyperbolaRadius_pos (ht.2.trans_lt hδr)).le⟩
  exact source_circles_of_two_components hh (hreg t htε) hcard D
    (negativePatchArc e r t) (fun i => e (negativeLevelArc t i 0))
    (fun i => mem_image_of_mem e (mem_image_of_mem _ hz)) hpatch hD hDdis

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

private theorem physical_model_chart (d : TerminalSaddleGeometry M P p e) :
    ∃ E : OpenPartialHomeomorph E2 S2,
      0 ∈ E.source ∧ E 0 = d.modelChart 0 ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ E E.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ E.symm E.target ∧
      E.source ⊆ e.source ∧
      ∀ x ∈ E.source, d.filledModel (E x) = g (e x) := by
  let k := Real.sqrt d.scale
  have hk : 0 < k := Real.sqrt_pos.mpr d.scale_pos
  let L : E2 ≃L[Real] E2 :=
    (LinearEquiv.smulOfNeZero Real E2 k⁻¹ (inv_ne_zero hk.ne')).toContinuousLinearEquiv
  let E₀ := d.modelChart.restrOpen (ball (0 : E2) d.matchingRadius) isOpen_ball
  let E := L.toHomeomorph.toOpenPartialHomeomorph.trans E₀
  have hEball (x : E2) (hx : x ∈ E.source) : L x ∈ closedBall 0 d.matchingRadius :=
    ball_subset_closedBall hx.2.2
  have hL (x : E2) : k • L x = x := by
    change k • (k⁻¹ • x) = x
    simp [smul_smul, hk.ne']
  have hEs : E.source ⊆ e.source := by
    intro x hx
    have hm := d.matching_actual_source (L x) (hEball x hx)
    change k • L x ∈ e.source at hm
    rwa [hL] at hm
  refine ⟨E, ?_, ?_, ?_, ?_, hEs, ?_⟩
  · change 0 ∈ (Set.univ : Set E2) ∧ L 0 ∈ d.modelChart.source ∩ ball 0 d.matchingRadius
    simpa only [map_zero, mem_inter_iff, mem_ball, dist_self] using
      And.intro (mem_univ (0 : E2)) ⟨d.modelChart_zero, d.matchingRadius_pos⟩
  · change d.modelChart (L 0) = d.modelChart 0
    rw [map_zero]
  · exact (d.modelChart_smooth.mono inter_subset_left).comp L.contDiff.contMDiff.contMDiffOn
      (fun _ hx => hx.2)
  · exact L.symm.contDiff.contMDiff.comp_contMDiffOn
      (d.modelChart_symm_smooth.mono (fun _ hx => hx.1.1))
  · intro x hx
    change d.transport (d.model (d.modelChart (L x))) = g (e x)
    rw [d.matching _ (hEball x hx)]
    change g (e (k • L x)) = g (e x)
    rw [hL]

private theorem ambient_sphere_embedding
    (G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞) :
    _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (fun q : S2 => G q) := by
  have hc := contMDiff_coe_sphere (n := 2) (m := ∞) (E := E3)
  apply isSmoothEmbedding_of_injective_mfderiv (G.contMDiff.comp hc)
    (G.injective.comp Subtype.val_injective)
  intro q
  rw [mfderiv_comp q ((G.contMDiff _).mdifferentiableAt (by simp))
    ((hc q).mdifferentiableAt (by simp))]
  apply (G.mfderivToContinuousLinearEquiv (by simp) _).injective.comp
  convert! injective_mvfderiv_subtypeVal_sphere (n := 2) q

private theorem planar_embedding_of_constant_height
    (k : S1 → E3) (hk : ContMDiff (𝓡 1) (𝓡 3) ∞ k)
    (hki : Injective k) (hkd : ∀ q, Injective (mfderiv (𝓡 1) (𝓡 3) k q))
    (z : Real) (hz : ∀ q, k q 2 = z) :
    _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (Saddle.toE2 ∘ k) := by
  have hp : ContMDiff (𝓡 3) (𝓡 2) ∞ Saddle.toE2 := by
    apply ContDiff.contMDiff
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · exact (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 3)).contDiff
    · exact (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 3)).contDiff
  have hl : ContMDiff (𝓡 2) (𝓡 3) ∞ (fun x => Saddle.toE3 x z) := by
    apply ContDiff.contMDiff
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · exact (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 2)).contDiff
    · exact (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 2)).contDiff
    · exact contDiff_const
  have heq : (fun x => Saddle.toE3 x z) ∘ (Saddle.toE2 ∘ k) = k := by
    funext q
    ext i
    fin_cases i <;> simp [Saddle.toE2, Saddle.toE3, hz, Function.comp_def]
  apply isSmoothEmbedding_of_injective_mfderiv (hp.comp hk)
  · intro q r hqr
    apply hki
    rw [← heq]
    exact congrArg (fun x => Saddle.toE3 x z) hqr
  · intro q
    have hd := hkd q
    rw [← heq, mfderiv_comp q ((hl _).mdifferentiableAt (by simp))
      (((hp.comp hk) q).mdifferentiableAt (by simp))] at hd
    intro u v huv
    apply hd
    exact congrArg (mfderiv (𝓡 2) (𝓡 3) (fun x => Saddle.toE3 x z)
      ((Saddle.toE2 ∘ k) q)) huv

private theorem project_model_source_circles
    (d : TerminalSaddleGeometry M P p e)
    (E : OpenPartialHomeomorph E2 S2)
    (hmatch : ∀ x ∈ E.source, d.filledModel (E x) = g (e x))
    {r t : Real} (hr : 0 < r) (ht : 0 < t) (htr : t < r ^ 2)
    (hrs : closedSquare r ⊆ E.source)
    (γ : Fin 2 → S1 → S2)
    (hγ : ∀ i, ContMDiff (𝓡 1) (𝓡 2) ∞ (γ i))
    (hγi : Injective (fun x : Fin 2 × S1 => γ x.1 x.2))
    (hγd : ∀ i q, Injective (mfderiv (𝓡 1) (𝓡 2) (γ i) q))
    (hcover : (⋃ i, range (γ i)) = {q : S2 | inner Real (M.v : E3) (d.filledModel q) =
      inner Real (M.v : E3) (g p) - t})
    (hpatch : ∀ i, negativePatchArc E r t i ⊆ range (γ i)) :
    ∃ C : Fin 2 → S1 → E2,
      (∀ i, _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (C i)) ∧
      Injective (fun x : Fin 2 × S1 => C x.1 x.2) ∧
      (⋃ i, range (C i)) = d.B (inner Real (M.v : E3) (g p) - t) ∧
      ∀ i s, s ∈ Icc (-hyperbolaRadius r t) (hyperbolaRadius r t) →
        Saddle.toE2 (d.flatten (g (e (negativeLevelArc t i s)))) ∈ range (C i) := by
  let z := inner Real (M.v : E3) (g p) - t
  let G := d.filledModel.trans d.flatten
  let k (i : Fin 2) : S1 → E3 := (fun q : S2 => G q) ∘ γ i
  let C (i : Fin 2) : S1 → E2 := Saddle.toE2 ∘ k i
  have hG := ambient_sphere_embedding G
  have hk (i : Fin 2) : ContMDiff (𝓡 1) (𝓡 3) ∞ (k i) := hG.contMDiff.comp (hγ i)
  have hki (i : Fin 2) : Injective (k i) := by
    intro q u hqu
    have heq : γ i q = γ i u := hG.isEmbedding.injective hqu
    exact congrArg Prod.snd (hγi (a₁ := (i,q)) (a₂ := (i,u)) heq)
  have hkd (i : Fin 2) (q : S1) : Injective (mfderiv (𝓡 1) (𝓡 3) (k i) q) := by
    dsimp [k]
    rw [mfderiv_comp q ((hG.contMDiff _).mdifferentiableAt (by simp))
      (((hγ i) q).mdifferentiableAt (by simp))]
    exact (injective_mfderiv_sphere_embedding hG _).comp (hγd i q)
  have hkheight (i : Fin 2) (q : S1) : k i q 2 = z := by
    change d.frame (d.D (d.filledModel (γ i q))) 2 = _
    rw [d.frame_height, d.D_height]
    exact hcover.subset (mem_iUnion_of_mem i (mem_range_self q))
  have hcoord (i : Fin 2) (q : S1) : Saddle.toE3 (C i q) z = k i q := by
    ext j
    fin_cases j <;> simp [C, Saddle.toE2, Saddle.toE3, hkheight, Function.comp_def]
  refine ⟨C, fun i => planar_embedding_of_constant_height (k i) (hk i) (hki i) (hkd i) z
    (hkheight i), ?_, ?_, ?_⟩
  · intro x y hxy
    apply hγi
    apply hG.isEmbedding.injective
    exact (hcoord x.1 x.2).symm.trans ((congrArg (fun x => Saddle.toE3 x z) hxy).trans
      (hcoord y.1 y.2))
  · ext x
    constructor
    · intro hx
      obtain ⟨i, q, rfl⟩ := by simpa only [mem_iUnion, mem_range] using hx
      refine ⟨d.filledModel (γ i q), ⟨γ i q, (γ i q).property, rfl⟩, ?_⟩
      exact (hcoord i q).symm
    · rintro ⟨_, ⟨q, hq, rfl⟩, heq⟩
      let q' : S2 := ⟨q, hq⟩
      have hh : inner Real (M.v : E3) (d.filledModel q') = z := by
        have hx := congrArg (fun y : E3 => y 2) heq
        change d.frame (d.D (d.filledModel q')) 2 = z at hx
        rwa [d.frame_height, d.D_height] at hx
      obtain ⟨i, u, hu⟩ := mem_iUnion.mp (hcover.superset hh)
      refine mem_iUnion_of_mem i ⟨u, ?_⟩
      change Saddle.toE2 (d.flatten (d.filledModel (γ i u))) = x
      rw [hu]
      change Saddle.toE2 (d.flatten (d.filledModel q)) = x
      rw [heq]
      ext j
      fin_cases j <;> rfl
  · intro i s hs
    obtain ⟨q, hq⟩ := hpatch i (mem_image_of_mem E (mem_image_of_mem _ hs))
    refine ⟨q, ?_⟩
    change Saddle.toE2 (d.flatten (d.filledModel (γ i q))) = _
    rw [hq, hmatch _ (hrs ((negativeLevelArc_mem_closedSquare hr ht htr i s).mpr hs))]

private theorem circle_pair_not_preconnected
    (C : Fin 2 → S1 → E2) (hC : ∀ i, Continuous (C i))
    (hinj : Injective (fun x : Fin 2 × S1 => C x.1 x.2)) :
    ¬ IsPreconnected (⋃ i, range (C i)) := by
  intro hc
  have hdis : Disjoint (range (C 0)) (range (C 1)) := by
    apply disjoint_left.mpr
    rintro x ⟨q, hq⟩ ⟨r, hr⟩
    have hi := congrArg Prod.fst (hinj (a₁ := (0,q)) (a₂ := (1,r)) (hq.trans hr.symm))
    exact (by decide : (0 : Fin 2) ≠ 1) hi
  have hcover : (⋃ i, range (C i)) ⊆ range (C 0) ∪ range (C 1) := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    fin_cases i
    · exact Or.inl hi
    · exact Or.inr hi
  have hs := isPreconnected_iff_subset_of_disjoint_closed.mp hc
    (range (C 0)) (range (C 1)) (isCompact_range (hC 0)).isClosed
    (isCompact_range (hC 1)).isClosed hcover (by rw [hdis.inter_eq, inter_empty])
  let q : S1 := ⟨EuclideanSpace.single 0 1, by simp⟩
  rcases hs with hs | hs
  · exact disjoint_left.mp hdis (hs (mem_iUnion_of_mem 1 (mem_range_self q))) (mem_range_self q)
  · exact disjoint_left.mp hdis (mem_range_self q) (hs (mem_iUnion_of_mem 0 (mem_range_self q)))

private theorem model_negative_branch_circle_pairs_of_band
    (d : TerminalSaddleGeometry M P p e)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2)
    (lo hi : Real)
    (hlower : lo < d.model (d.modelChart 0) 2)
    (hupper : d.model (d.modelChart 0) 2 ≤ hi)
    (hrawunique : ∀ q : S2, d.model q 2 ∈ Icc lo hi →
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q : S2 => d.model q 2) q = 0 → q = d.modelChart 0)
    (hrawconnected : IsPreconnected {q : S2 | d.model q 2 = d.model (d.modelChart 0) 2}) :
    ∃ r δ : Real, 0 < r ∧ closedSquare r ⊆ e.source ∧
      0 < δ ∧ δ < d.eta ∧ δ < r ^ 2 ∧
      ∀ t ∈ Ioc (0 : Real) δ,
        ∃ C : Fin 2 → S1 → E2,
          (∀ i, _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (C i)) ∧
          Injective (fun x : Fin 2 × S1 => C x.1 x.2) ∧
          (⋃ i, range (C i)) = d.B (inner Real (M.v : E3) (g p) - t) ∧
          ∀ i s, s ∈ Icc (-hyperbolaRadius r t) (hyperbolaRadius r t) →
            Saddle.toE2 (d.flatten (g (e (negativeLevelArc t i s)))) ∈ range (C i) := by
  let c := inner Real (M.v : E3) (g p)
  let p₀ := d.modelChart 0
  let F : S2 → E3 := fun q => d.filledModel q
  let h : S2 → Real := fun q => inner Real (M.v : E3) (F q)
  let h₀ : S2 → Real := fun q => d.model q 2
  have hF : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ F :=
    ambient_sphere_embedding d.filledModel
  have hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h :=
    (innerSL Real (M.v : E3)).contMDiff.comp hF.contMDiff
  have hheight (q : S2) : h q = c + d.scale * (h₀ q - h₀ p₀) := d.transport_height _
  have hcenter : h p₀ = c := by rw [hheight]; ring
  let J : Real → Real := fun x => (x - c) / d.scale + h₀ p₀
  have hJ : ContDiff Real ∞ J := by dsimp [J]; fun_prop
  have hraw : h₀ = J ∘ h := by
    funext q
    dsimp [J, Function.comp_def]
    rw [hheight]
    field_simp [d.scale_pos.ne']; ring
  have hcrit (q : S2) (hq : mfderiv (𝓡 2) 𝓘(Real, Real) h q = 0) :
      mfderiv (𝓡 2) 𝓘(Real, Real) h₀ q = 0 := by
    rw [hraw, mfderiv_comp q ((hJ.contMDiff _).mdifferentiableAt (by simp))
      ((hh q).mdifferentiableAt (by simp)), hq]
    ext x
    simp
  have hunique (q : S2) (hq : h q = h p₀)
      (hc : mfderiv (𝓡 2) 𝓘(Real, Real) h q = 0) : q = p₀ := by
    have heq : h₀ q = h₀ p₀ := by rw [hheight, hcenter] at hq; nlinarith [d.scale_pos]
    exact hrawunique q (by change h₀ q ∈ Icc lo hi; rw [heq]; exact ⟨hlower.le, hupper⟩)
      (hcrit q hc)
  have hconnected : IsPreconnected {q : S2 | h q = h p₀} := by
    have heq : {q : S2 | h q = h p₀} = {q : S2 | h₀ q = h₀ p₀} := by
      ext q
      simp only [mem_ofPred_eq, hheight]
      constructor <;> intro hq <;> nlinarith [d.scale_pos]
    rw [heq]
    exact hrawconnected
  obtain ⟨E, hE0, hEp, hE, hEi, hEs, hmatch⟩ := physical_model_chart d
  have hformE (x : E2) (hx : x ∈ E.source) : h (E x) = h p₀ - x 0 ^ 2 + x 1 ^ 2 := by
    change inner Real (M.v : E3) (d.filledModel (E x)) = _
    rw [hmatch x hx, hform x (hEs hx), hcenter]
  obtain ⟨ε₀, hε₀, hcircles⟩ := exists_model_lower_slice_circle_pair d hform
  let ε := min ε₀ (min (d.scale * (h₀ p₀ - lo) / 2) d.eta)
  have hε : 0 < ε := lt_min hε₀
    (lt_min (half_pos (mul_pos d.scale_pos (sub_pos.mpr hlower))) d.eta_pos)
  have hεη : ε ≤ d.eta := (min_le_right _ _).trans (min_le_right _ _)
  have hε₀le : ε ≤ ε₀ := min_le_left _ _
  have hεlo : ε ≤ d.scale * (h₀ p₀ - lo) / 2 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hreg (t : Real) (ht : t ∈ Ioc (0 : Real) ε) (q : S2)
      (hq : h q = h p₀ - t) : mfderiv (𝓡 2) 𝓘(Real, Real) h q ≠ 0 := by
    intro hc
    have hqheight := hheight q
    rw [hcenter] at hq
    have hqlo : lo ≤ h₀ q := by nlinarith [ht.2.trans hεlo, d.scale_pos]
    have hupper' : h₀ p₀ ≤ hi := hupper
    have hqhi : h₀ q ≤ hi := by nlinarith [d.scale_pos, ht.1]
    have heq := hrawunique q ⟨hqlo, hqhi⟩ (hcrit q hc)
    change q = p₀ at heq
    rw [heq, hcenter] at hq
    linarith [ht.1]
  have hnot (t : Real) (ht : t ∈ Ioc (0 : Real) ε) :
      ¬ IsPreconnected {q : S2 | h q = h p₀ - t} := by
    intro hpconn
    obtain ⟨C, hC, hi, hcov⟩ := hcircles (-t) ⟨by linarith [ht.2.trans hε₀le], by linarith [ht.1]⟩
    have hB : IsPreconnected (d.B (c - t)) :=
      (model_slice_preconnected_iff d _).mpr (by simpa only [hcenter] using hpconn)
    rw [sub_eq_add_neg, ← hcov] at hB
    exact circle_pair_not_preconnected C (fun i => (hC i).contMDiff.continuous) hi hB
  obtain ⟨r, δ, hr, hrs, hδ, hδε, hδr, hγ⟩ := negative_branch_source_circles F hF
    M.v (norm_eq_of_mem_sphere M.v) p₀ hunique hconnected E hE0 hEp hE hEi hformE hε hreg hnot
  refine ⟨r, δ, hr, hrs.trans hEs, hδ, hδε.trans_le hεη, hδr, ?_⟩
  intro t ht
  obtain ⟨γ, hγs, hγi, hγd, hcover, hpatch⟩ := hγ t ht
  apply project_model_source_circles d E hmatch hr ht.1 (ht.2.trans_lt hδr) hrs γ hγs hγi hγd
    _ hpatch
  change (⋃ i, range (γ i)) = {q : S2 | h q = h p₀ - t} at hcover
  rw [hcenter] at hcover
  exact hcover




theorem exists_model_negative_branch_circle_pairs
    (d : TerminalSaddleGeometry M P p e)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2) :
    ∃ r δ : Real, 0 < r ∧ closedSquare r ⊆ e.source ∧
      0 < δ ∧ δ < d.eta ∧ δ < r ^ 2 ∧
      ∀ t ∈ Ioc (0 : Real) δ,
        ∃ C : Fin 2 → S1 → E2,
          (∀ i, _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (C i)) ∧
          Injective (fun x : Fin 2 × S1 => C x.1 x.2) ∧
          (⋃ i, range (C i)) = d.B (inner Real (M.v : E3) (g p) - t) ∧
          ∀ i s, s ∈ Icc (-hyperbolaRadius r t) (hyperbolaRadius r t) →
            Saddle.toE2 (d.flatten (g (e (negativeLevelArc t i s)))) ∈ range (C i) := by
  rcases d.model_kind with hmodel | hmodel
  · have hcenter := terminal_standard_model_chart_center d hmodel hform
    have hh : d.model (d.modelChart 0) 2 = -1 := by
      rw [hmodel, hcenter]
      exact Saddle.height_saddlePoint
    apply model_negative_branch_circle_pairs_of_band d hform (-9 / 8) (1 / 2)
      (by rw [hh]; norm_num) (by rw [hh]; norm_num)
    · intro q hq hc
      rw [hmodel] at hq hc
      rw [hcenter]
      exact (Saddle.critical_in_band_iff q hq).mp hc
    · rw [hh, hmodel]
      exact standard_critical_level_preconnected
  · have hc := terminal_model_chart_critical d hform
    rw [hmodel] at hc
    have hz := terminal_nested_model_chart_latitude d hmodel hform
    obtain ⟨q, hqz, hqh, hqc, _⟩ := Saddle.Nested.exists_unique_critical_point_in_height_band
    have hqp : q = d.modelChart 0 := Saddle.Nested.critical_latitude_unique_in_saddle_interval
      hqc hc (Ioo_subset_Icc_self hqz) (Ioo_subset_Icc_self hz)
    rw [hqp] at hqh
    apply model_negative_branch_circle_pairs_of_band d hform 1 (13 / 10)
    · rw [hmodel]
      exact hqh.1
    · rw [hmodel]
      change Saddle.Nested.height (d.modelChart 0) ≤ _
      linarith [hqh.2]
    · intro q hq hqcrit
      rw [hmodel] at hq hqcrit
      exact (Saddle.Nested.critical_in_height_band_iff_eq_saddle hc hz q hq).mp hqcrit
    · rw [hmodel]
      exact (Saddle.Nested.isConnected_critical_level_of_saddle_latitude hc hz).isPreconnected

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

end

end M38Schoenflies
