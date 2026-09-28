import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Continuation.FixedChart
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Continuation.Speed









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]


theorem coordinate_geodesic_unique_germ_at
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {q₁ w₁ q₂ w₂ : ℝ → E} {t₀ : ℝ}
    (hB : ContDiffAt ℝ ∞ B (q₁ t₀)) (hinv : (B (q₁ t₀)).IsInvertible)
    (hq : q₁ t₀ = q₂ t₀) (hw : w₁ t₀ = w₂ t₀)
    (hd₁ : ∀ᶠ t in 𝓝 t₀, HasDerivAt q₁ (w₁ t) t ∧
      HasDerivAt w₁ (-coordinateChristoffel B (q₁ t) (w₁ t) (w₁ t)) t)
    (hd₂ : ∀ᶠ t in 𝓝 t₀, HasDerivAt q₂ (w₂ t) t ∧
      HasDerivAt w₂ (-coordinateChristoffel B (q₂ t) (w₂ t) (w₂ t)) t) :
    ∀ᶠ t in 𝓝 t₀, q₁ t = q₂ t ∧ w₁ t = w₂ t := by
  have hV := contDiffAt_coordinateGeodesicField hB hinv (z := (q₁ t₀, w₁ t₀))
  obtain ⟨K, S, hS, hLip⟩ :=
    (hV.of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞)).exists_lipschitzOnWith
  have hmem₁ : ∀ᶠ t in 𝓝 t₀, (q₁ t, w₁ t) ∈ S :=
    ((hd₁.self_of_nhds).1.continuousAt.prodMk
      (hd₁.self_of_nhds).2.continuousAt).preimage_mem_nhds hS
  have hmem₂ : ∀ᶠ t in 𝓝 t₀, (q₂ t, w₂ t) ∈ S := by
    apply ((hd₂.self_of_nhds).1.continuousAt.prodMk
      (hd₂.self_of_nhds).2.continuousAt).preimage_mem_nhds
    simpa only [hq, hw] using hS
  have heq := ODE_solution_unique_of_eventually
    (v := fun _ : ℝ => coordinateGeodesicField B) (s := fun _ : ℝ => S)
    (K := K) (t₀ := t₀) (Eventually.of_forall (fun _ => hLip))
    (hd₁.and hmem₁ |>.mono fun t ht => ⟨ht.1.1.prodMk ht.1.2, ht.2⟩)
    (hd₂.and hmem₂ |>.mono fun t ht => ⟨ht.1.1.prodMk ht.1.2, ht.2⟩)
    (show (q₁ t₀, w₁ t₀) = (q₂ t₀, w₂ t₀) by rw [hq, hw])
  exact heq.mono fun t ht => ⟨congrArg Prod.fst ht, congrArg Prod.snd ht⟩

end PoincareConjecture

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem IsGeodesicOn.eq_nhds_of_eq_and_coordDeriv
    {g : RiemannianMetric n M} {γ η : ℝ → M} {s : Set ℝ}
    (hγ : g.IsGeodesicOn γ s) (hη : g.IsGeodesicOn η s)
    (hs : IsOpen s) (p : M)
    (hγmap : MapsTo γ s (extChartAt (𝓡 n) p).source)
    (hηmap : MapsTo η s (extChartAt (𝓡 n) p).source)
    {t₀ : ℝ} (ht₀ : t₀ ∈ s) (hpos : γ t₀ = η t₀)
    (hvel : deriv (fun t => extChartAt (𝓡 n) p (γ t)) t₀ =
      deriv (fun t => extChartAt (𝓡 n) p (η t)) t₀) :
    γ =ᶠ[𝓝 t₀] η := by
  let c := extChartAt (𝓡 n) p
  let B := g.pullbackCoefficients c.symm
  let q₁ := fun t : ℝ => c (γ t)
  let q₂ := fun t : ℝ => c (η t)
  have hqmem : q₁ t₀ ∈ c.target := c.map_source (hγmap ht₀)
  have hB : ContDiffAt ℝ ∞ B (q₁ t₀) :=
    (g.contDiffOn_chartCoefficients p (q₁ t₀) hqmem).contDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 n) p).mem_nhds hqmem)
  have hinv : (B (q₁ t₀)).IsInvertible := g.isInvertible_chartCoefficients p hqmem
  have hd₁ := Filter.Eventually.mono (hs.mem_nhds ht₀) (fun t ht =>
    hγ.hasDerivAt_in_chart hs p hγmap t ht)
  have hd₂ := Filter.Eventually.mono (hs.mem_nhds ht₀) (fun t ht =>
    hη.hasDerivAt_in_chart hs p hηmap t ht)
  have heq := coordinate_geodesic_unique_germ_at hB hinv
    (congrArg c hpos) hvel hd₁ hd₂
  filter_upwards [heq, hs.mem_nhds ht₀] with t ht hts
  exact c.injOn (hγmap hts) (hηmap hts) ht.1


theorem IsGeodesicOn.exists_open_nhds
    {g : RiemannianMetric n M} {γ : ℝ → M} {s : Set ℝ}
    (hγ : g.IsGeodesicOn γ s) {t : ℝ} (ht : t ∈ s) :
    ∃ U : Set ℝ, IsOpen U ∧ t ∈ U ∧ g.IsGeodesicOn γ U := by
  obtain ⟨p, q, w, hlocal⟩ := hγ t ht
  obtain ⟨U, hUsub, hUopen, htU⟩ :=
    mem_nhds_iff.mp (eventually_eventually_nhds.mpr hlocal)
  exact ⟨U, hUopen, htU, fun u hu => ⟨p, q, w, hUsub hu⟩⟩


theorem IsGeodesicOn.contMDiffAt
    {g : RiemannianMetric n M} {γ : ℝ → M} {s : Set ℝ}
    (hγ : g.IsGeodesicOn γ s) {t : ℝ} (ht : t ∈ s) :
    ContMDiffAt (𝓘(ℝ, ℝ)) (𝓡 n) 1 γ t := by
  obtain ⟨U, hUopen, htU, hU⟩ := hγ.exists_open_nhds ht
  exact hU.contMDiffOn.contMDiffAt (hUopen.mem_nhds htU)



theorem IsGeodesicOn.exists_common_chart_nhds
    {g : RiemannianMetric n M} {γ η : ℝ → M} {s : Set ℝ}
    (hγ : g.IsGeodesicOn γ s) (hη : g.IsGeodesicOn η s)
    {t : ℝ} (ht : t ∈ s) (p : M)
    (hγp : γ t ∈ (extChartAt (𝓡 n) p).source)
    (hηp : η t ∈ (extChartAt (𝓡 n) p).source) :
    ∃ U : Set ℝ, IsOpen U ∧ t ∈ U ∧
      g.IsGeodesicOn γ U ∧ g.IsGeodesicOn η U ∧
      MapsTo γ U (extChartAt (𝓡 n) p).source ∧
      MapsTo η U (extChartAt (𝓡 n) p).source := by
  obtain ⟨Uγ, hUγopen, htγ, hUγ⟩ := hγ.exists_open_nhds ht
  obtain ⟨Uη, hUηopen, htη, hUη⟩ := hη.exists_open_nhds ht
  have hsrcγ : ∀ᶠ u in 𝓝 t, γ u ∈ (extChartAt (𝓡 n) p).source :=
    (hγ.contMDiffAt ht).continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source (I := 𝓡 n) p).mem_nhds hγp)
  have hsrcη : ∀ᶠ u in 𝓝 t, η u ∈ (extChartAt (𝓡 n) p).source :=
    (hη.contMDiffAt ht).continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source (I := 𝓡 n) p).mem_nhds hηp)
  obtain ⟨U, hUsub, hUopen, htU⟩ := mem_nhds_iff.mp
    ((hsrcγ.and hsrcη).and (inter_mem (hUγopen.mem_nhds htγ) (hUηopen.mem_nhds htη)))
  exact ⟨U, hUopen, htU, fun u hu => hUγ u (hUsub hu).2.1,
    fun u hu => hUη u (hUsub hu).2.2,
    fun u hu => (hUsub hu).1.1, fun u hu => (hUsub hu).1.2⟩


theorem IsGeodesicOn.eq_nhds_of_initial_data
    {g : RiemannianMetric n M} {γ η : ℝ → M} {s : Set ℝ}
    (hγ : g.IsGeodesicOn γ s) (hη : g.IsGeodesicOn η s)
    {t₀ : ℝ} (ht₀ : t₀ ∈ s) (p : M)
    (hp : γ t₀ ∈ (extChartAt (𝓡 n) p).source) (hpos : γ t₀ = η t₀)
    (hvel : deriv (fun t => extChartAt (𝓡 n) p (γ t)) t₀ =
      deriv (fun t => extChartAt (𝓡 n) p (η t)) t₀) :
    γ =ᶠ[𝓝 t₀] η := by
  obtain ⟨U, hUopen, htU, hγU, hηU, hγmap, hηmap⟩ :=
    hγ.exists_common_chart_nhds hη ht₀ p hp (hpos ▸ hp)
  exact hγU.eq_nhds_of_eq_and_coordDeriv hηU hUopen p hγmap hηmap htU hpos hvel



theorem IsGeodesicOn.eq_nhds_on_of_eq_nhds [T2Space M]
    {g : RiemannianMetric n M} {γ η : ℝ → M} {s : Set ℝ}
    (hγ : g.IsGeodesicOn γ s) (hη : g.IsGeodesicOn η s)
    (hs : IsPreconnected s) {t₀ : ℝ} (ht₀ : t₀ ∈ s)
    (heq : γ =ᶠ[𝓝 t₀] η) :
    ∀ t ∈ s, γ =ᶠ[𝓝 t] η := by
  let G : Set ℝ := {t | γ =ᶠ[𝓝 t] η}
  have hGopen : IsOpen G := isOpen_setOfPred_eventually_nhds
  have hGclosed : closure G ∩ s ⊆ G := by
    intro t ht
    have hfreq : ∃ᶠ u in 𝓝 t, u ∈ G := mem_closure_iff_frequently.mp ht.1
    have hpos : γ t = η t := tendsto_nhds_unique_of_frequently_eq
      (hγ.contMDiffAt ht.2).continuousAt (hη.contMDiffAt ht.2).continuousAt
      (hfreq.mono fun u hu => hu.self_of_nhds)
    let p := γ t
    have hγp : γ t ∈ (extChartAt (𝓡 n) p).source := mem_extChartAt_source p
    obtain ⟨U, hUopen, htU, hγU, hηU, hγmap, hηmap⟩ :=
      hγ.exists_common_chart_nhds hη ht.2 p hγp (hpos ▸ hγp)
    have hγd := (hγU.hasDerivAt_in_chart hUopen p hγmap t htU).2.continuousAt
    have hηd := (hηU.hasDerivAt_in_chart hUopen p hηmap t htU).2.continuousAt
    have hvel : deriv (fun u => extChartAt (𝓡 n) p (γ u)) t =
        deriv (fun u => extChartAt (𝓡 n) p (η u)) t := by
      apply tendsto_nhds_unique_of_frequently_eq hγd hηd
      exact hfreq.mono fun u hu =>
        (hu.fun_comp (extChartAt (𝓡 n) p)).deriv_eq
    exact hγU.eq_nhds_of_eq_and_coordDeriv hηU hUopen p hγmap hηmap htU hpos hvel
  exact hs.subset_of_closure_inter_subset hGopen ⟨t₀, ht₀, heq⟩ hGclosed


theorem IsGeodesicOn.eqOn_of_eq_nhds [T2Space M]
    {g : RiemannianMetric n M} {γ η : ℝ → M} {s : Set ℝ}
    (hγ : g.IsGeodesicOn γ s) (hη : g.IsGeodesicOn η s)
    (hs : IsPreconnected s) {t₀ : ℝ} (ht₀ : t₀ ∈ s)
    (heq : γ =ᶠ[𝓝 t₀] η) : EqOn γ η s :=
  fun t ht => (hγ.eq_nhds_on_of_eq_nhds hη hs ht₀ heq t ht).self_of_nhds



theorem IsGeodesicOn.eqOn_of_eventuallyEq [T2Space M]
    {g : RiemannianMetric n M} {γ η : ℝ → M} {s : Set ℝ}
    (hγ : g.IsGeodesicOn γ s) (hη : g.IsGeodesicOn η s)
    (_hsopen : IsOpen s) (hs : IsPreconnected s) {t₀ : ℝ} (ht₀ : t₀ ∈ s)
    (heq : γ =ᶠ[𝓝 t₀] η) : EqOn γ η s :=
  hγ.eqOn_of_eq_nhds hη hs ht₀ heq



theorem IsGeodesicOn.eq_nhds_on_of_initial_data [T2Space M]
    {g : RiemannianMetric n M} {γ η : ℝ → M} {s : Set ℝ}
    (hγ : g.IsGeodesicOn γ s) (hη : g.IsGeodesicOn η s)
    (hs : IsPreconnected s) {t₀ : ℝ} (ht₀ : t₀ ∈ s) (p : M)
    (hp : γ t₀ ∈ (extChartAt (𝓡 n) p).source) (hpos : γ t₀ = η t₀)
    (hvel : deriv (fun t => extChartAt (𝓡 n) p (γ t)) t₀ =
      deriv (fun t => extChartAt (𝓡 n) p (η t)) t₀) :
    ∀ t ∈ s, γ =ᶠ[𝓝 t] η :=
  hγ.eq_nhds_on_of_eq_nhds hη hs ht₀
    (hγ.eq_nhds_of_initial_data hη ht₀ p hp hpos hvel)

end PoincareConjecture.RiemannianMetric
