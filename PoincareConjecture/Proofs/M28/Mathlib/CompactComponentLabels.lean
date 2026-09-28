import PoincareConjecture.Proofs.M28.Mathlib.ComponentLabels
import PoincareConjecture.Proofs.M07.Topology.Exhaustion










set_option autoImplicit false

open Set Filter
open scoped Topology




theorem IsCompact.exists_connected_envelope_within
    {X : Type*} [TopologicalSpace X] [T2Space X]
    [LocallyConnectedSpace X] [LocallyCompactSpace X] [SecondCountableTopology X]
    {K C : Set X} (hK : IsCompact K) (hKC : K ⊆ C)
    (hCopen : IsOpen C) (hC : IsConnected C) {a : X} (ha : a ∈ C) :
    ∃ A : Set X, IsConnected A ∧ a ∈ A ∧ K ⊆ A ∧
      IsCompact (closure A) ∧ closure A ⊆ C := by
  let : PreconnectedSpace C := Subtype.preconnectedSpace hC.isPreconnected
  let : LocallyConnectedSpace C := hCopen.locallyConnectedSpace
  let : LocallyCompactSpace C := hCopen.locallyCompactSpace
  let K' : Set C := Subtype.val ⁻¹' K
  have hK' : IsCompact K' := by
    apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
    simpa only [K', image_preimage_eq_inter_range, Subtype.range_val,
      inter_eq_left.mpr hKC] using hK
  obtain ⟨U, hUopen, hUconn, hUcompact, hUstep, hUcover, hUa⟩ :=
    Poincare.exists_connected_open_exhaustion (⟨a, ha⟩ : C)
  have hUmono : Monotone U := monotone_nat_of_le_succ hUstep
  obtain ⟨j, hj⟩ := hK'.elim_directed_cover U hUopen
    (by rw [hUcover]; exact subset_univ _) hUmono.directed_le
  let A : Set X := Subtype.val '' U j
  let Q : Set X := Subtype.val '' closure (U j)
  have hQ : IsCompact Q := (hUcompact j).image continuous_subtype_val
  have hAQ : closure A ⊆ Q :=
    closure_minimal (image_mono subset_closure) hQ.isClosed
  refine ⟨A, (hUconn j).image _ continuous_subtype_val.continuousOn,
    ⟨⟨a, ha⟩, hUa j, rfl⟩, ?_, hQ.of_isClosed_subset isClosed_closure hAQ, ?_⟩
  · intro x hx
    exact ⟨⟨x, hKC hx⟩, hj hx, rfl⟩
  · intro x hx
    obtain ⟨y, _, rfl⟩ := hAQ hx
    exact y.property





theorem IsCompact.eventually_component_mem_iff
    {X : Type*} [TopologicalSpace X] [T2Space X]
    [LocallyConnectedSpace X] [LocallyCompactSpace X] [SecondCountableTopology X]
    {Y : ℕ → Type*} [∀ k, TopologicalSpace (Y k)]
    (V : ℕ → Set X) (hopen : ∀ k, IsOpen (V k)) (hmono : Monotone V)
    (hcover : (⋃ k, V k) = univ) {S : Set X} {j : ℕ} (hS : S ⊆ V j)
    (e : ∀ k, X → Y k) (T : ∀ k, Set (Y k))
    (hcont : ∀ k, ContinuousOn (e k) (V k))
    (hinj : ∀ k, InjOn (e k) (V k))
    (hmap : ∀ k, MapsTo (e k) (V k) (T k))
    {C K : Set X} (hK : IsCompact K) (hKC : K ⊆ C)
    (hCopen : IsOpen C) (hC : IsConnected C) (hCS : C ⊆ Sᶜ)
    {a : X} (ha : a ∈ C) :
    ∀ᶠ k in atTop, ∀ F : Set (Y k),
      (∀ z ∈ F, connectedComponentIn (T k \ e k '' S) z = F) →
      ∀ x ∈ K, (e k x ∈ F ↔ e k a ∈ F) := by
  obtain ⟨A, hA, haA, hKA, hcompact, hAC⟩ :=
    hK.exists_connected_envelope_within hKC hCopen hC ha
  obtain ⟨l, hl⟩ := hcompact.elim_directed_cover V hopen
    (by rw [hcover]; exact subset_univ _) hmono.directed_le
  filter_upwards [eventually_ge_atTop (max j l)] with k hk
  intro F hF x hx
  have hSK : S ⊆ V k := hS.trans (hmono ((le_max_left _ _).trans hk))
  have hAK : A ⊆ V k := subset_closure.trans (hl.trans
    (hmono ((le_max_right _ _).trans hk)))
  have himage : e k '' A ⊆ T k \ e k '' S := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨hmap k (hAK hy), ?_⟩
    rintro ⟨z, hz, heq⟩
    have hzy : z = y := hinj k (hSK hz) (hAK hy) heq
    exact hCS (hAC (subset_closure hy)) (hzy ▸ hz)
  have hconnected := hA.isPreconnected.image (e k) ((hcont k).mono hAK)
  exact hconnected.mem_iff_of_connectedComponentIn_eq himage hF
    (mem_image_of_mem _ (hKA hx)) (mem_image_of_mem _ haA)
