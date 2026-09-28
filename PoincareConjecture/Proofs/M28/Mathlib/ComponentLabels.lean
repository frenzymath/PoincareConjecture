import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Compactness.Compact
import Mathlib.Order.Filter.AtTopBot.Basic

set_option autoImplicit false

open Set Filter
open scoped Topology

theorem IsPreconnected.mem_iff_of_connectedComponentIn_eq
    {X : Type*} [TopologicalSpace X] {A U F : Set X}
    (hA : IsPreconnected A) (hAU : A ⊆ U)
    (hF : ∀ z ∈ F, _root_.connectedComponentIn U z = F)
    {x y : X} (hx : x ∈ A) (hy : y ∈ A) : x ∈ F ↔ y ∈ F := by
  constructor
  · intro hxF
    exact hF x hxF ▸ hA.subset_connectedComponentIn hx hAU hy
  · intro hyF
    exact hF y hyF ▸ hA.subset_connectedComponentIn hy hAU hx

theorem JoinedIn.eventually_component_mem_iff
    {X : Type*} [TopologicalSpace X] {Y : ℕ → Type*}
    [∀ k, TopologicalSpace (Y k)]
    (V : ℕ → Set X) (hopen : ∀ k, IsOpen (V k)) (hmono : Monotone V)
    (hcover : (⋃ k, V k) = univ) {S : Set X} {j : ℕ} (hS : S ⊆ V j)
    (e : ∀ k, X → Y k) (T : ∀ k, Set (Y k))
    (hcont : ∀ k, ContinuousOn (e k) (V k))
    (hinj : ∀ k, InjOn (e k) (V k))
    (hmap : ∀ k, MapsTo (e k) (V k) (T k)) {x₀ x₁ : X}
    (hpath : JoinedIn Sᶜ x₀ x₁) :
    ∀ᶠ k in atTop, ∀ F : Set (Y k),
      (∀ z ∈ F, connectedComponentIn (T k \ e k '' S) z = F) →
      (e k x₀ ∈ F ↔ e k x₁ ∈ F) := by
  obtain ⟨γ, hγ⟩ := hpath
  have hcompact : IsCompact (range γ) := isCompact_range γ.continuous
  obtain ⟨l, hl⟩ := hcompact.elim_directed_cover V hopen (by rw [hcover]; exact subset_univ _)
    hmono.directed_le
  filter_upwards [eventually_ge_atTop (max j l)] with k hk
  intro F hF
  have hSK : S ⊆ V k := hS.trans (hmono ((le_max_left _ _).trans hk))
  have hK : range γ ⊆ V k := hl.trans (hmono ((le_max_right _ _).trans hk))
  have himage : e k '' range γ ⊆ T k \ e k '' S := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨hmap k (hK hx), ?_⟩
    rintro ⟨z, hz, heq⟩
    have hzx : z = x := hinj k (hSK hz) (hK hx) heq
    obtain ⟨t, rfl⟩ := hx
    exact hγ t (hzx ▸ hz)
  have hconnected : IsPreconnected (e k '' range γ) :=
    (isPreconnected_range γ.continuous).image (e k) ((hcont k).mono hK)
  have hx₀ : e k x₀ ∈ e k '' range γ :=
    mem_image_of_mem _ ⟨0, γ.source⟩
  have hx₁ : e k x₁ ∈ e k '' range γ :=
    mem_image_of_mem _ ⟨1, γ.target⟩
  exact hconnected.mem_iff_of_connectedComponentIn_eq himage hF hx₀ hx₁

theorem not_joinedIn_of_eventually_opposite_component_labels
    {X : Type*} [TopologicalSpace X] {Y : ℕ → Type*}
    [∀ k, TopologicalSpace (Y k)]
    (V : ℕ → Set X) (hopen : ∀ k, IsOpen (V k)) (hmono : Monotone V)
    (hcover : (⋃ k, V k) = univ) {S : Set X} {j : ℕ} (hS : S ⊆ V j)
    (e : ∀ k, X → Y k) (T : ∀ k, Set (Y k))
    (hcont : ∀ k, ContinuousOn (e k) (V k))
    (hinj : ∀ k, InjOn (e k) (V k))
    (hmap : ∀ k, MapsTo (e k) (V k) (T k)) {x₀ x₁ : X}
    (hlabels : ∀ᶠ k in atTop, ∃ F : Set (Y k),
      (∀ z ∈ F, connectedComponentIn (T k \ e k '' S) z = F) ∧
      (e k x₀ ∈ F ↔ e k x₁ ∉ F)) :
    ¬ JoinedIn Sᶜ x₀ x₁ := by
  intro hpath
  have htail := hpath.eventually_component_mem_iff V hopen hmono hcover hS e T hcont hinj hmap
  obtain ⟨k, hk, F, hF, hopposite⟩ := (htail.and hlabels).exists
  have hsame := hk F hF
  tauto
