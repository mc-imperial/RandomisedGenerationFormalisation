import Mathlib
import RandomisedGeneration.Generator
import RandomisedGeneration.Language

namespace RandomisedGeneration

def greedilyGenerableLanguages {Γ : Type u}
  [Inhabited Γ] [FinEnum Γ] : Set (Language Γ) :=
  { L | ∃ (Γw Q : Type u)
          (_ : FinEnum Γw)
          (_ : DecidableEq Q)
          (gen : Generator Γw Γ Q)
          (S : Finset Q)
          (hS : GeneratorSupports gen S),
    gen.IsGreedy ∧ generatedLanguage gen S hS = L }

/-- Given a generator, produce a greedy version that always moves the input head right.
    The state is augmented with `Option Bool`: `none` means we're in sync with the
    input tape, `some b` means we've read ahead and `b` is the next bit the original
    generator should see.

    The greedified generator produces the same language as the original. -/
def Generator.greedify {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo]
    (gen : Generator Γw Γo Q) : Generator Γw Γo (Q × Option Bool) where
  init := (gen.init, none)
  blank := gen.blank
  δ := fun (q, buf) inputBit w =>
    let effectiveBit := buf.getD inputBit
    match gen.δ q effectiveBit w with
    | none => none
    | some (q', w', o, itd, wd) =>
      match itd with
      | InputTapeDirection.R => some ((q', none), w', o, InputTapeDirection.R, wd)
      | InputTapeDirection.N => some ((q', some effectiveBit), w', o, InputTapeDirection.R, wd)

lemma Generator.greedify_isGreedy {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo]
    (gen : Generator Γw Γo Q) : gen.greedify.IsGreedy := by
  intro ⟨q, buf⟩ b w q' w' o itd wd h
  unfold greedify at h
  simp only at h
  split at h
  · simp at h
  · split at h <;> simp_all

lemma GeneratorSupports_greedify {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo]
    (gen : Generator Γw Γo Q)
    (S : Finset Q) (hS : GeneratorSupports gen S) :
    GeneratorSupports gen.greedify (S ×ˢ Finset.univ) := by
  constructor
  · -- init ∈ S ×ˢ univ
    simp only [GeneratorSupports, Bool.forall_bool, Generator.greedify, Finset.mem_product,
      Finset.mem_univ, and_true] at *
    exact hS.1
  · -- closure under δ
    intro ⟨q, buf⟩ hq b w ⟨q', buf'⟩ w' o itd wd hδ
    simp only [Generator.greedify] at hδ
    simp only [Finset.mem_product, Finset.mem_univ, and_true] at hq ⊢
    split at hδ
    · simp at hδ
    · rename_i q'' w'' o'' itd'' wd'' hgen
      split at hδ <;> simp only [Option.some.injEq, Prod.mk.injEq] at hδ
      all_goals (obtain ⟨⟨rfl, _⟩, rfl, rfl, rfl, rfl⟩ := hδ; exact hS.2 q hq _ _ _ _ _ _ _ hgen)

/-- If gen computes w on some input, then gen.greedify computes w on some input. -/
lemma greedify_of_computes {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo]
    (gen : Generator Γw Γo Q) {f : ℕ → Bool} {w : List Γo} :
    Computes gen (initConfig gen f) w →
    ∃ g, Computes gen.greedify (initConfig gen.greedify g) w := by
  intro hComp
  suffices ∀ (cfg : GenConfig Γw Γo Q) (w : List Γo),
      Computes gen cfg w →
      ∀ (gcfg : GenConfig Γw Γo (Q × Option Bool)),
        gcfg.state.1 = cfg.state →
        gcfg.work = cfg.work →
        gcfg.workIndex = cfg.workIndex →
        gcfg.output = cfg.output →
        gcfg.state.2.getD (gcfg.input gcfg.inputIndex) = cfg.input cfg.inputIndex →
        ∃ g, (∀ k, k < gcfg.inputIndex → g k = gcfg.input k) ∧
          g gcfg.inputIndex = gcfg.input gcfg.inputIndex ∧
          Computes gen.greedify { gcfg with input := g } w by
    obtain ⟨g, _, _, hg⟩ := this _ _ hComp (initConfig gen.greedify f)
      (by simp [initConfig, Generator.greedify])
      (by simp [initConfig, Generator.greedify])
      (by simp [initConfig, Generator.greedify])
      (by simp [initConfig, Generator.greedify])
      (by simp [initConfig, Generator.greedify])
    exact ⟨g, by simpa [initConfig, Generator.greedify] using hg⟩
  intro cfg w hComp'
  induction hComp' with
  | halt cfg hHalt =>
    intro gcfg hState hWork hWIdx hOut hEff
    refine ⟨gcfg.input, fun k _ => rfl, rfl, ?_⟩
    rw [show { gcfg with input := gcfg.input } = gcfg from by simp]
    rw [hOut]; apply Computes.halt
    unfold step at hHalt ⊢
    unfold Generator.greedify
    simp only
    rw [hState, hWork, hWIdx, hEff]
    cases hδ : gen.δ cfg.state (cfg.input cfg.inputIndex) (cfg.work cfg.workIndex) with
    | none => simp
    | some val => simp [hδ] at hHalt
  | step cfg cfg' w hStep _ ih =>
    intro gcfg hState hWork hWIdx hOut hEff
    unfold step at hStep
    cases hδ : gen.δ cfg.state (cfg.input cfg.inputIndex) (cfg.work cfg.workIndex) with
    | none => simp [hδ] at hStep
    | some val =>
      obtain ⟨q', w', o, itd, wd⟩ := val
      simp only [hδ] at hStep
      simp only [Option.some.injEq] at hStep
      -- Extract cfg' fields from hStep
      have hState' : cfg'.state = q' := by rw [← hStep]
      have hInput' : cfg'.input = cfg.input := by rw [← hStep]
      have hWork' : cfg'.work = fun x => if x = cfg.workIndex then w' else cfg.work x := by
        rw [← hStep]
      have hWIdx' : cfg'.workIndex = cfg.workIndex + ↑wd := by rw [← hStep]
      have hOut' : cfg'.output = match o with
        | none => cfg.output | some g => cfg.output ++ [g] := by
          cases o <;> simp [← hStep]
      have hIIdx' : cfg'.inputIndex = cfg.inputIndex + ↑itd := by rw [← hStep]
      cases itd with
      | R =>
        -- Original advances. Greedify also advances, buf cleared.
        let gcfg' : GenConfig Γw Γo (Q × Option Bool) := {
          state := (q', none),
          input := gcfg.input,
          inputIndex := gcfg.inputIndex + 1,
          work := fun x => if x = gcfg.workIndex then w' else gcfg.work x,
          workIndex := gcfg.workIndex + ↑wd,
          output := match o with | none => gcfg.output | some g => gcfg.output ++ [g] }
        -- Need: gcfg'.state.2.getD (gcfg'.input gcfg'.inputIndex) = cfg'.input cfg'.inputIndex
        -- i.e., gcfg.input (gcfg.inputIndex + 1) = cfg.input (cfg.inputIndex + 1)
        -- We don't know this, so use Function.update
        let newBit := cfg.input (cfg.inputIndex + 1)
        let gcfg'' : GenConfig Γw Γo (Q × Option Bool) := {
          gcfg' with input := Function.update gcfg.input (gcfg.inputIndex + 1) newBit }
        obtain ⟨g, hgPast, hgCur, hgComp⟩ := ih gcfg''
          (by simp [gcfg'', gcfg', hState'])
          (by simp [gcfg'', gcfg', hWork, hWIdx, hWork'])
          (by simp [gcfg'', gcfg', hWIdx, hWIdx'])
          (by simp [gcfg'', gcfg', hOut, hOut']; cases o <;> simp)
          (by
            simp only [gcfg'', gcfg', Function.update, Option.getD]
            rw [hInput', hIIdx']
            simp [newBit]
          )
        refine ⟨g, ?_, ?_, ?_⟩
        · intro k hk
          have := hgPast k (by simp [gcfg'', gcfg']; omega)
          rw [this]
          simp [gcfg'', Function.update, show k ≠ gcfg.inputIndex + 1 from by omega]
        · have := hgPast gcfg.inputIndex (by simp [gcfg'', gcfg'])
          rw [this]
          simp [gcfg'', Function.update]
        · apply Computes.step _ _ _ _ hgComp
          unfold step Generator.greedify
          simp only
          have hgEq : g gcfg.inputIndex = gcfg.input gcfg.inputIndex := by
            have := hgPast gcfg.inputIndex (by simp [gcfg'', gcfg'])
            rw [this]; simp [gcfg'', Function.update]
          have hgEff : gcfg.state.2.getD (g gcfg.inputIndex) = cfg.input cfg.inputIndex := by
            rw [hgEq, hEff]
          rw [hState, hWork, hWIdx, hgEff, hδ]
          simp only [Option.some.injEq]
          ext
          · simp [gcfg'', gcfg']
          · rfl
          · simp
          · simp only [gcfg'', gcfg']
          · simp only [gcfg'', gcfg', hWIdx]
            split
            · rfl
            · exact (congr_fun hWork _).symm
          · simp [gcfg'', gcfg', hWIdx]
          · simp [gcfg'', gcfg', hOut]
            cases o <;> rfl
      | N =>
        -- Original stays. Greedify advances and buffers.
        let gcfg' : GenConfig Γw Γo (Q × Option Bool) := {
          state := (q', some (cfg.input cfg.inputIndex)),
          input := gcfg.input,
          inputIndex := gcfg.inputIndex + 1,
          work := fun x => if x = gcfg.workIndex then w' else gcfg.work x,
          workIndex := gcfg.workIndex + ↑wd,
          output := match o with | none => gcfg.output | some g => gcfg.output ++ [g] }
        -- effectiveBit for next step: buf = some (cfg.input cfg.inputIndex)
        -- cfg'.inputIndex = cfg.inputIndex (didn't advance)
        -- cfg'.input cfg'.inputIndex = cfg.input cfg.inputIndex
        -- gcfg'.state.2.getD (...) = cfg.input cfg.inputIndex ✓
        obtain ⟨g, hgPast, hgCur, hgComp⟩ := ih gcfg'
          (by simp [gcfg', hState'])
          (by simp [gcfg', hWork, hWIdx, hWork'])
          (by simp [gcfg', hWIdx, hWIdx'])
          (by simp [gcfg', hOut, hOut']; cases o <;> simp)
          (by
            simp only [gcfg', Option.getD]
            rw [hInput', hIIdx']
            simp)
        refine ⟨g, ?_, ?_, ?_⟩
        · intro k hk
          have := hgPast k (by simp [gcfg']; omega)
          rw [this]
        · have := hgPast gcfg.inputIndex (by simp [gcfg'])
          rw [this]
        · apply Computes.step _ _ _ _ hgComp
          unfold step Generator.greedify
          simp only
          have hgEq : g gcfg.inputIndex = gcfg.input gcfg.inputIndex := by
            have := hgPast gcfg.inputIndex (by simp [gcfg'])
            rw [this]
          have hgEff : gcfg.state.2.getD (g gcfg.inputIndex) = cfg.input cfg.inputIndex := by
            rw [hgEq, hEff]
          rw [hState, hWork, hWIdx, hgEff, hδ]
          simp only [Option.some.injEq]
          ext
          · simp [gcfg']
          · rfl
          · simp
          · simp [gcfg']
          · simp only [gcfg', hWIdx]
            split
            · rfl
            · exact (congr_fun hWork _).symm
          · simp [gcfg', hWIdx]
          · simp [gcfg', hOut]
            cases o <;> rfl

/-- If gen.greedify computes w on some input, then gen computes w on some input. -/
lemma computes_of_greedify {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo]
    (gen : Generator Γw Γo Q) {g : ℕ → Bool} {w : List Γo} :
    Computes gen.greedify (initConfig gen.greedify g) w →
    ∃ f, Computes gen (initConfig gen f) w := by
  intro hComp
  suffices ∀ (gcfg : GenConfig Γw Γo (Q × Option Bool)) (w : List Γo),
      Computes gen.greedify gcfg w →
      ∀ (cfg : GenConfig Γw Γo Q),
        cfg.state = gcfg.state.1 →
        cfg.work = gcfg.work →
        cfg.workIndex = gcfg.workIndex →
        cfg.output = gcfg.output →
        cfg.input cfg.inputIndex = gcfg.state.2.getD (gcfg.input gcfg.inputIndex) →
        ∃ f, (∀ k, k < cfg.inputIndex → f k = cfg.input k) ∧
          f cfg.inputIndex = cfg.input cfg.inputIndex ∧
          Computes gen { cfg with input := f } w by
    obtain ⟨f, _, _, hf⟩ := this _ _ hComp (initConfig gen g)
      (by simp [initConfig, Generator.greedify])
      (by simp [initConfig, Generator.greedify])
      (by simp [initConfig, Generator.greedify])
      (by simp [initConfig, Generator.greedify])
      (by simp [initConfig, Generator.greedify])
    exact ⟨f, by simpa [initConfig] using hf⟩
  intro gcfg w hgComp
  induction hgComp with
  | halt gcfg hHalt =>
    intro cfg hState hWork hWIdx hOut hEff
    refine ⟨cfg.input, fun k _ => rfl, rfl, ?_⟩
    rw [show { cfg with input := cfg.input } = cfg from by simp]
    rw [hOut]; apply Computes.halt
    unfold step at hHalt ⊢
    unfold Generator.greedify at hHalt
    simp only at hHalt
    rw [hState, hWork, hWIdx, hEff]
    split at hHalt
    · cases hδ : gen.δ gcfg.state.1 (gcfg.state.2.getD (gcfg.input gcfg.inputIndex))
        (gcfg.work gcfg.workIndex) with
      | none => rfl
      | some val =>
        rename_i heq _
        simp only [Int.reduceNeg, reduceCtorEq]
        rename_i hGreedifyNone
        simp only [hδ] at hGreedifyNone
        split at hGreedifyNone <;> exact absurd hGreedifyNone (Option.some_ne_none _)
    · simp at hHalt
  | step gcfg gcfg' w hStep _ ih =>
    intro cfg hState hWork hWIdx hOut hEff
    unfold step at hStep
    unfold Generator.greedify at hStep
    simp only at hStep
    cases hδ : gen.δ gcfg.state.1 (gcfg.state.2.getD (gcfg.input gcfg.inputIndex))
        (gcfg.work gcfg.workIndex) with
    | none => simp [hδ] at hStep
    | some val =>
      obtain ⟨q', w', o, itd, wd⟩ := val
      simp only [hδ] at hStep
      cases itd with
      | N =>
        -- Original stays. Greedify buffers effectiveBit.
        -- gcfg' has buf = some effectiveBit, inputIndex advanced.
        -- cfg' has same inputIndex (didn't advance).
        simp only at hStep
        have hGcfg' := hStep  -- extract gcfg' fields
        let cfg' : GenConfig Γw Γo Q := {
          state := q',
          input := cfg.input,
          inputIndex := cfg.inputIndex,
          work := fun x => if x = cfg.workIndex then w' else cfg.work x,
          workIndex := cfg.workIndex + ↑wd,
          output := match o with | none => cfg.output | some g => cfg.output ++ [g] }
        -- The effective bit condition passes through: buf = some effectiveBit,
        -- cfg'.inputIndex = cfg.inputIndex, so cfg'.input cfg'.inputIndex = hEff
        obtain ⟨f, hfPast, hfCur, hfComp⟩ := ih cfg'
          (by
            simp only [Option.some.injEq] at hStep
            subst hStep
            rfl
          )
          (by
            simp only [Option.some.injEq] at hStep
            subst hStep
            simp [cfg', hWork, hWIdx]
          )
          (by
            simp only [Option.some.injEq] at hStep
            subst hStep
            simp [cfg', hWIdx]
          )
          (by
            simp only [Option.some.injEq] at hStep
            subst hStep
            simp [cfg', hOut]
            cases o <;> rfl
          )
          (by
            simp only [Option.some.injEq] at hStep
            subst hStep
            simp only [Option.getD, cfg']
            change cfg.input cfg.inputIndex = gcfg.state.2.getD (gcfg.input gcfg.inputIndex)
            exact hEff
          )  -- effectiveBit condition: same as hEff
        refine ⟨f, ?_, ?_, ?_⟩
        · exact hfPast  -- past positions: same since inputIndex didn't change
        · exact hfCur
        · apply Computes.step _ _ _ _ hfComp
          -- step gen { cfg with input := f } = some { cfg' with input := f }
          unfold step
          rw [show ({ cfg with input := f } : GenConfig Γw Γo Q).state = cfg.state from rfl]
          rw [hState, hWork, hWIdx]
          rw [show ({ cfg with input := f } : GenConfig Γw Γo Q).input
            ({ cfg with input := f } : GenConfig Γw Γo Q).inputIndex = f cfg.inputIndex from rfl]
          rw [hfCur, hEff, hδ]
          simp only [add_zero, Int.reduceNeg, Option.some.injEq, GenConfig.mk.injEq, true_and]
          refine ⟨rfl, rfl, ?_, ?_, ?_⟩
          · ext x; simp [cfg', hWork, hWIdx]
          · simp [cfg', hWIdx]
          · cases o <;> simp [cfg', hOut]
      | R =>
        -- Original advances. Greedify clears buf.
        -- gcfg' has buf = none, inputIndex advanced.
        -- cfg' has inputIndex advanced.
        simp only at hStep
        let newBit := gcfg.input (gcfg.inputIndex + 1)
        let cfg' : GenConfig Γw Γo Q := {
          state := q',
          input := Function.update cfg.input (cfg.inputIndex + 1) newBit,
          inputIndex := cfg.inputIndex + 1,
          work := fun x => if x = cfg.workIndex then w' else cfg.work x,
          workIndex := cfg.workIndex + ↑wd,
          output := match o with | none => cfg.output | some g => cfg.output ++ [g] }
        obtain ⟨f, hfPast, hfCur, hfComp⟩ := ih cfg'
          (by
            simp only [Option.some.injEq] at hStep
            subst hStep
            rfl
          )
          (by
            simp only [Option.some.injEq] at hStep
            subst hStep
            simp [cfg', hWork, hWIdx]
          )
          (by
            simp only [Option.some.injEq] at hStep
            subst hStep
            simp [cfg', hWIdx]
          )
          (by
            simp only [Option.some.injEq] at hStep
            subst hStep
            simp [cfg', hOut]
            cases o <;> rfl
          )
          (by
            simp only [Option.some.injEq] at hStep
            subst hStep
            simp [cfg', Function.update, Option.getD]
            rfl
          )  -- effectiveBit: buf = none, so g(gcfg'.inputIndex) = f(cfg'.inputIndex)
        refine ⟨f, ?_, ?_, ?_⟩
        · -- f agrees with cfg.input at positions < cfg.inputIndex
          intro k hk
          have := hfPast k (by
            change k < cfg.inputIndex + 1; omega
          )
          rw [this]
          simp [cfg', Function.update, show k ≠ cfg.inputIndex + 1 from by omega]
        · -- f cfg.inputIndex = cfg.input cfg.inputIndex
          -- f agrees at positions < cfg.inputIndex + 1, so at cfg.inputIndex
          have := hfPast cfg.inputIndex (by
            change cfg.inputIndex < cfg.inputIndex + 1; omega
          )
          rw [this]
          simp [cfg', Function.update]
        · apply Computes.step _ _ _ _ hfComp
          unfold step
          rw [show ({ cfg with input := f } : GenConfig Γw Γo Q).state = cfg.state from rfl]
          rw [hState, hWork, hWIdx]
          rw [show ({ cfg with input := f } : GenConfig Γw Γo Q).input
            ({ cfg with input := f } : GenConfig Γw Γo Q).inputIndex = f cfg.inputIndex from rfl]
          -- f cfg.inputIndex = cfg.input cfg.inputIndex (just proved above)
          -- cfg.input cfg.inputIndex = effectiveBit (from hEff)
          have hfEff : f cfg.inputIndex = gcfg.state.2.getD (gcfg.input gcfg.inputIndex) := by
            have := hfPast cfg.inputIndex (by change cfg.inputIndex < cfg.inputIndex + 1; omega)
            rw [this]
            simp only [Function.update, Nat.left_eq_add, one_ne_zero, ↓reduceDIte, cfg']
            exact hEff
          rw [hfEff, hδ]
          simp only [Option.some.injEq]
          ext
          · simp [cfg']
          · rfl
          · simp [cfg']
          · simp only [cfg', hWIdx]
            congr 1
            exact congr_fun hWork.symm _
          · simp [cfg', hWIdx]
          · cases o <;> simp [cfg', hOut]

lemma generatedLanguage_greedify {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo]
    (gen : Generator Γw Γo Q)
    (S : Finset Q) (hS : GeneratorSupports gen S) :
    generatedLanguage gen S hS =
    generatedLanguage gen.greedify (S ×ˢ Finset.univ) (GeneratorSupports_greedify gen S hS) := by
  ext w
  simp only [generatedLanguage, Set.mem_setOf_eq]
  constructor
  · rintro ⟨f, hComp⟩
    obtain ⟨g, hComp'⟩ := greedify_of_computes gen hComp
    exact ⟨g, hComp'⟩
  · rintro ⟨g, hComp⟩
    obtain ⟨f, hComp'⟩ := computes_of_greedify gen hComp
    exact ⟨f, hComp'⟩

theorem greedilyGenerable_eq_generable {Γ : Type u}
  [Inhabited Γ] [FinEnum Γ] :
  greedilyGenerableLanguages (Γ := Γ) = generableLanguages := by
  apply Set.Subset.antisymm
  · -- greedilyGenerableLanguages ⊆ generableLanguages
    intro L ⟨Γw, Q, hΓw, hQ, gen, S, hS, _, hL⟩
    exact ⟨Γw, Q, hΓw, hQ, gen, S, hS, hL⟩
  · -- generable ⊆ greedy: greedify the generator
    intro L ⟨Γw, Q, hΓw, hQ, gen, S, hS, hL⟩
    exact ⟨Γw, Q × Option Bool, inferInstance, inferInstance,
      gen.greedify, S ×ˢ Finset.univ, GeneratorSupports_greedify gen S hS,
      gen.greedify_isGreedy,
      by rw [← generatedLanguage_greedify gen S hS]; exact hL⟩

end RandomisedGeneration
