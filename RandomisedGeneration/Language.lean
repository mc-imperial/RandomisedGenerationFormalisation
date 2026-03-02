import Mathlib
import Mathlib.Computability.Halting
import Mathlib.Computability.PostTuringMachine
import Mathlib.Computability.TuringMachine
import RandomisedGeneration.Generator

open Function (update)

namespace RandomisedGeneration

@[reducible]
def Language (Γ : Type u)
[Inhabited Γ] [FinEnum Γ]
 : Type u := Set (List Γ)

def generatedLanguage {Γw Γo Q : Type u}
  [FinEnum Γw] [Inhabited Γo] [FinEnum Γo]
  (gen : Generator Γw Γo Q)
  (S : Finset Q)
  (_ : GeneratorSupports gen S) : Language Γo :=
  { out | ∃ input, Computes gen (initConfig gen input) out }

lemma Generator.restrictToSupport_generatedLanguage {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo]
    (gen : Generator Γw Γo Q)
    (S : Finset Q) (hS : GeneratorSupports gen S) :
    generatedLanguage (gen.restrictToSupport S hS) Finset.univ
      (generator_supports_univ _) =
    generatedLanguage gen S hS := by
  ext w
  simp only [generatedLanguage, Set.mem_setOf_eq]
  constructor
  · rintro ⟨input, h_comp⟩
    exact ⟨input, restrictToSupport_Computes_lift gen S hS h_comp⟩
  · rintro ⟨input, h_comp⟩
    exact ⟨input, restrictToSupport_Computes gen S hS h_comp⟩

def generableLanguages {Γ : Type u}
  [Inhabited Γ] [FinEnum Γ] : Set (Language Γ) :=
  { L | ∃ (Γw Q : Type u)
          (_ : FinEnum Γw)
          (hQdec : DecidableEq Q)
          (gen : Generator Γw Γ Q)
          (S : Finset Q)
          (hS : GeneratorSupports gen S),
    generatedLanguage gen S hS = L }

def languagesRecognisedByTM0s {Γ : Type u}
    [Inhabited Γ] [FinEnum Γ] : Set (Language Γ) :=
  { L | ∃ (Γ' : Type u)
          (_ : Inhabited Γ')
          (_ : Fintype Γ')
          (_ : DecidableEq Γ')
          (enc : Γ → Γ')
          (_ : Function.Injective enc)
          (_ : default ∉ Set.range enc)
          (Λ : Type u)
          (_ : Inhabited Λ)
          (M : Turing.TM0.Machine (Γ := Γ') (Λ := Λ))
          (S : Finset Λ)
          (_ : Turing.TM0.Supports M S),
    L = { input | (Turing.TM0.eval M (input.map enc)).Dom } }

def languagesRecognisedByTM1s {Γ : Type u} [Inhabited Γ] [FinEnum Γ] : Set (Language Γ) :=
  { L | ∃ (Γ' : Type u)
          (_ : Inhabited Γ')
          (_ : Fintype Γ')
          (_ : DecidableEq Γ')
          (enc : Γ → Γ')
          (_ : Function.Injective enc)
          (_ : default ∉ Set.range enc)
          (Λ : Type u)
          (_ : Inhabited Λ)
          (σ : Type u)
          (_ : Inhabited σ)
          (_ : Fintype σ)
          (M : Λ → Turing.TM1.Stmt Γ' Λ σ)
          (S : Finset Λ)
          (_ : Turing.TM1.Supports M S),
        L = { input | (Turing.TM1.eval M (input.map enc)).Dom } }

def languagesRecognisedByTM2s {Γ : Type u} [Inhabited Γ] [FinEnum Γ] : Set (Language Γ) :=
  { L | ∃ (K : Type u)
          (_ : Inhabited K)
          (_ : Fintype K)
          (_ : DecidableEq K)
          (Γ' : K → Type u)
          (_ : ∀ k, Inhabited (Γ' k))
          (_ : ∀ k, Fintype (Γ' k))
          (_ : ∀ k, DecidableEq (Γ' k))
          (h : Γ' default = Γ)
          (Λ : Type u)
          (_ : Inhabited Λ)
          (σ : Type u)
          (_ : Inhabited σ)
          (_ : Fintype σ)
          (M : Λ → Turing.TM2.Stmt Γ' Λ σ)
          (S : Finset Λ)
          (_ : Turing.TM2.Supports M S),
        L = { input | (Turing.TM2.eval M default (h ▸ input.reverse)).Dom } }

lemma every_tm1_recognisable_language_is_tm0_recognisable {Γ : Type u}
    [Inhabited Γ] [FinEnum Γ]
    (L : Language Γ)
    (hL : L ∈ languagesRecognisedByTM1s) :
    L ∈ languagesRecognisedByTM0s := by
  obtain ⟨Γ', hΓ'inh, hΓ'fin, hΓ'dec, enc, henc_inj, henc_blank, Λ,
    hΛinh, σ, hσinh, hσfin, M, S, hS, hL_eq⟩ := hL
  refine ⟨Γ', hΓ'inh, hΓ'fin, hΓ'dec, enc, henc_inj, henc_blank,
          Turing.TM1to0.Λ' M, inferInstance,
          Turing.TM1to0.tr M,
          Turing.TM1to0.trStmts M S,
          Turing.TM1to0.tr_supports M hS,
          ?_⟩
  rw [hL_eq]
  unfold Language
  ext input
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hdom
    rwa [Turing.TM1to0.tr_eval M (List.map enc input)]
  · intro hdom
    rwa [← Turing.TM1to0.tr_eval M (List.map enc input)]

inductive FixThenSimLabel (Λ2to1 : Type u) [Inhabited Λ2to1]
  | fix   -- the single fix-up state
  | sim (l : Λ2to1)  -- delegate to M2to1

def relabel {Γ : Type*} {Λ Λ' : Type*} {σ : Type*}
    (f : Λ → Λ') : Turing.TM1.Stmt Γ Λ σ → Turing.TM1.Stmt Γ Λ' σ
  | Turing.TM1.Stmt.move d q     =>
      Turing.TM1.Stmt.move d (relabel f q)
  | Turing.TM1.Stmt.write g q    =>
      Turing.TM1.Stmt.write g (relabel f q)
  | Turing.TM1.Stmt.load g q     =>
      Turing.TM1.Stmt.load g (relabel f q)
  | Turing.TM1.Stmt.branch p q r =>
      Turing.TM1.Stmt.branch p (relabel f q) (relabel f r)
  | Turing.TM1.Stmt.goto l       =>
      Turing.TM1.Stmt.goto (fun a s => f (l a s))
  | Turing.TM1.Stmt.halt         =>
      Turing.TM1.Stmt.halt

def fixThenSim
    {K : Type u} {Γ : K → Type u} {Λ σ : Type u}
    [Inhabited Λ] [DecidableEq K]
    (M2to1 : Turing.TM2to1.Λ' K Γ Λ σ → Turing.TM1.Stmt (Turing.TM2to1.Γ' K Γ)
      (Turing.TM2to1.Λ' K Γ Λ σ) σ) :
    FixThenSimLabel (Turing.TM2to1.Λ' K Γ Λ σ) →
      Turing.TM1.Stmt (Turing.TM2to1.Γ' K Γ) (FixThenSimLabel (Turing.TM2to1.Λ' K Γ Λ σ)) σ
  | FixThenSimLabel.fix =>
      Turing.TM1.Stmt.write (fun a _ => (true, a.2))
      <| Turing.TM1.Stmt.goto (fun _ _ => FixThenSimLabel.sim default)
  | FixThenSimLabel.sim l =>
      relabel FixThenSimLabel.sim (M2to1 l)

instance {Λ2to1 : Type*} [Inhabited Λ2to1] : Inhabited (FixThenSimLabel Λ2to1) :=
  ⟨FixThenSimLabel.fix⟩

lemma Turing.TM1.SupportsStmt_relabel {Γ : Type*} {Λ Λ' : Type*} {σ : Type*}
    (f : Λ → Λ') (S : Finset Λ) (S' : Finset Λ')
    (hf : ∀ l ∈ S, f l ∈ S')
    (q : Turing.TM1.Stmt Γ Λ σ)
    (hq : Turing.TM1.SupportsStmt S q) :
    Turing.TM1.SupportsStmt S' (relabel f q) := by
  induction q with
  | move d q ih => exact ih hq
  | write g q ih => exact ih hq
  | load g q ih => exact ih hq
  | branch p q r ihq ihr => exact ⟨ihq hq.1, ihr hq.2⟩
  | goto l => exact fun a s => hf _ (hq a s)
  | halt => trivial

deriving instance DecidableEq for FixThenSimLabel

lemma fixThenSim_supports
    {K : Type u} {Γ : K → Type u} {Λ σ : Type u}
    [Inhabited Λ] [DecidableEq K]
    (M2 : Λ → Turing.TM2.Stmt Γ Λ σ)
    (S2to1 : Finset (Turing.TM2to1.Λ' K Γ Λ σ))
    (hS : Turing.TM1.Supports (Turing.TM2to1.tr M2) S2to1) :
    ∃ S : Finset (FixThenSimLabel (Turing.TM2to1.Λ' K Γ Λ σ)),
      Turing.TM1.Supports (fixThenSim (Turing.TM2to1.tr M2)) S := by
  refine ⟨S2to1.map ⟨FixThenSimLabel.sim, fun a b h => ?_⟩
    |>.cons FixThenSimLabel.fix (by simp), ?_⟩
  · -- injectivity of FixThenSimLabel.sim
    cases h; rfl
  · constructor
    · -- default = FixThenSimLabel.fix is in the support set
      change FixThenSimLabel.fix ∈ _
      simp
    · intro l hl
      simp only [Finset.mem_cons, Finset.mem_map, Function.Embedding.coeFn_mk] at hl
      rcases hl with rfl | ⟨l', hl', rfl⟩
      · -- FixThenSimLabel.fix case
        simp only [fixThenSim, Turing.TM1.SupportsStmt]
        intro a s
        simp only [Finset.mem_cons, Finset.mem_map, Function.Embedding.coeFn_mk]
        exact Or.inr ⟨default, hS.1, rfl⟩
      · -- FixThenSimLabel.sim l' case
        simp only [fixThenSim]
        apply Turing.TM1.SupportsStmt_relabel FixThenSimLabel.sim
        · intro l'' hl''
          simp only [Finset.mem_cons, Finset.mem_map, Function.Embedding.coeFn_mk]
          exact Or.inr ⟨l'', hl'', rfl⟩
        · exact hS.2 l' hl'

def trInitAllFalse {K : Type u}
[DecidableEq K]
{Γ : K → Type u} (k : K) (L : List (Γ k)) : List (Turing.TM2to1.Γ' K Γ) :=
  L.reverse.map fun a ↦ (false, update (fun _ ↦ none) k (some a))

lemma relabel_step
    {K : Type u} {Γ : K → Type u} {Λ σ : Type u}
    [Inhabited Λ] [Inhabited σ] [DecidableEq K]
    (M2to1 : Turing.TM2to1.Λ' K Γ Λ σ → Turing.TM1.Stmt (Turing.TM2to1.Γ' K Γ)
      (Turing.TM2to1.Λ' K Γ Λ σ) σ)
    (c : Turing.TM1.Cfg (Turing.TM2to1.Γ' K Γ) (Turing.TM2to1.Λ' K Γ Λ σ) σ) :
    Turing.TM1.step (fixThenSim M2to1)
      ⟨c.l.map FixThenSimLabel.sim, c.var, c.Tape⟩ =
    (Turing.TM1.step M2to1 c).map
      (fun c' => ⟨c'.l.map FixThenSimLabel.sim, c'.var, c'.Tape⟩) := by
  have key : ∀ (q : Turing.TM1.Stmt (Turing.TM2to1.Γ' K Γ) (Turing.TM2to1.Λ' K Γ Λ σ) σ)
      (v : σ) (T : Turing.Tape (Turing.TM2to1.Γ' K Γ)),
      Turing.TM1.stepAux (relabel FixThenSimLabel.sim q) v T =
      let r := Turing.TM1.stepAux q v T
      ⟨r.l.map FixThenSimLabel.sim, r.var, r.Tape⟩ := by
    intro q
    induction q with
    | move d q ih => simp [Turing.TM1.stepAux, relabel, ih]
    | write g q ih => simp [Turing.TM1.stepAux, relabel, ih]
    | load g q ih => simp [Turing.TM1.stepAux, relabel, ih]
    | branch p q r ihq ihr =>
      intro v T
      simp only [Turing.TM1.stepAux, relabel]
      cases p T.1 v <;> simp [ihq, ihr]
    | goto l => simp [Turing.TM1.stepAux, relabel]
    | halt => simp [Turing.TM1.stepAux, relabel]
  simp only [Turing.TM1.step, fixThenSim]
  cases c with | mk cl cv cT =>
    cases cl with
    | none => simp
    | some l =>
      simp only [Option.map_some]
      rw [key (M2to1 l) cv cT]

-- The fix step produces exactly the tr M initial config (with sim-wrapped label)
lemma fix_step
    {K : Type u} {Γ : K → Type u} {Λ σ : Type u}
    [Inhabited Λ] [Inhabited σ] [DecidableEq K]
    (M : Λ → Turing.TM2.Stmt Γ Λ σ) (k : K) (L : List (Γ k)) :
    Turing.TM1.step (fixThenSim (Turing.TM2to1.tr M))
      (Turing.TM1.init (trInitAllFalse k L)) =
    some ⟨some (FixThenSimLabel.sim (default : Turing.TM2to1.Λ' K Γ Λ σ)), default,
              (Turing.TM1.init (Turing.TM2to1.trInit k L) :
                Turing.TM1.Cfg (Turing.TM2to1.Γ' K Γ) (Turing.TM2to1.Λ' K Γ Λ σ) σ).Tape⟩ := by
  simp only [Turing.TM1.step, Turing.TM1.init, Turing.TM1.stepAux, fixThenSim]
  congr 1

lemma sim_wrapped_of_reaches
    {K : Type u} {Γ : K → Type u} {Λ σ : Type u}
    [Inhabited Λ] [Inhabited σ] [DecidableEq K]
    (M2to1 : Turing.TM2to1.Λ' K Γ Λ σ → Turing.TM1.Stmt (Turing.TM2to1.Γ' K Γ)
      (Turing.TM2to1.Λ' K Γ Λ σ) σ)
    (a : Turing.TM1.Cfg (Turing.TM2to1.Γ' K Γ) (Turing.TM2to1.Λ' K Γ Λ σ) σ)
    (c : Turing.TM1.Cfg (Turing.TM2to1.Γ' K Γ) (FixThenSimLabel (Turing.TM2to1.Λ' K Γ Λ σ)) σ) :
    Turing.Reaches (Turing.TM1.step (fixThenSim M2to1))
      ⟨a.l.map FixThenSimLabel.sim, a.var, a.Tape⟩ c →
    ∃ a' : Turing.TM1.Cfg (Turing.TM2to1.Γ' K Γ) (Turing.TM2to1.Λ' K Γ Λ σ) σ,
      c = ⟨a'.l.map FixThenSimLabel.sim, a'.var, a'.Tape⟩ := by
  intro h
  induction h with
  | refl => exact ⟨a, rfl⟩
  | tail _ step ih =>
    obtain ⟨a', rfl⟩ := ih
    -- step : next ∈ TM1.step (fixThenSim M2to1) ⟨a'.l.map FixThenSimLabel.sim, a'.var, a'.Tape⟩
    -- use relabel_step to show next is sim-wrapped
    rw [Option.mem_def, relabel_step] at step
    simp only [Option.map_eq_some_iff] at step
    obtain ⟨a'', ha'', rfl⟩ := step
    exact ⟨a'', rfl⟩

lemma relabel_reaches
    {K : Type u} {Γ : K → Type u} {Λ σ : Type u}
    [Inhabited Λ] [Inhabited σ] [DecidableEq K]
    (M2to1 : Turing.TM2to1.Λ' K Γ Λ σ → Turing.TM1.Stmt (Turing.TM2to1.Γ' K Γ)
      (Turing.TM2to1.Λ' K Γ Λ σ) σ)
    (a b : Turing.TM1.Cfg (Turing.TM2to1.Γ' K Γ) (Turing.TM2to1.Λ' K Γ Λ σ) σ) :
    Turing.Reaches (Turing.TM1.step M2to1) a b →
    Turing.Reaches (Turing.TM1.step (fixThenSim M2to1))
      ⟨a.l.map FixThenSimLabel.sim, a.var, a.Tape⟩
      ⟨b.l.map FixThenSimLabel.sim, b.var, b.Tape⟩ := by
  intro h
  induction h with
  | refl => exact .refl
  | tail _ step ih =>
    apply Relation.ReflTransGen.tail ih
    rw [Option.mem_def, relabel_step, step]
    simp

lemma relabel_reaches_inv
    {K : Type u} {Γ : K → Type u} {Λ σ : Type u}
    [Inhabited Λ] [Inhabited σ] [DecidableEq K]
    (M2to1 : Turing.TM2to1.Λ' K Γ Λ σ → Turing.TM1.Stmt (Turing.TM2to1.Γ' K Γ)
      (Turing.TM2to1.Λ' K Γ Λ σ) σ)
    (a b : Turing.TM1.Cfg (Turing.TM2to1.Γ' K Γ) (Turing.TM2to1.Λ' K Γ Λ σ) σ) :
    Turing.Reaches (Turing.TM1.step (fixThenSim M2to1))
      ⟨a.l.map FixThenSimLabel.sim, a.var, a.Tape⟩
      ⟨b.l.map FixThenSimLabel.sim, b.var, b.Tape⟩ →
    Turing.Reaches (Turing.TM1.step M2to1) a b := by
  intro h
  have hgen : ∀ (x y : Turing.TM1.Cfg (Turing.TM2to1.Γ' K Γ)
        (FixThenSimLabel (Turing.TM2to1.Λ' K Γ Λ σ)) σ),
      Turing.Reaches (Turing.TM1.step (fixThenSim M2to1)) x y →
      ∀ (a b : Turing.TM1.Cfg (Turing.TM2to1.Γ' K Γ) (Turing.TM2to1.Λ' K Γ Λ σ) σ),
        x = ⟨a.l.map FixThenSimLabel.sim, a.var, a.Tape⟩ →
        y = ⟨b.l.map FixThenSimLabel.sim, b.var, b.Tape⟩ →
        Turing.Reaches (Turing.TM1.step M2to1) a b := by
    intro x y hxy
    induction hxy with
    | refl =>
      intro a b hx hy
      have hab : a = b := by
        cases a; cases b
        simp only at hx hy
        obtain ⟨hl, hv, hT⟩ := hx
        simp only [Turing.TM1.Cfg.mk.injEq] at hy
        obtain ⟨hl, hv, hT⟩ := hy
        simp [Option.map_injective (fun x y h => by cases h; rfl) hl, hv, hT]
      subst hab; exact .refl
    | tail _ hstep ih =>
      intro a b hx hy
      rw [Option.mem_def] at hstep
      rename_i a_outer b_outer b_mid c_final b_reach
      obtain ⟨mid, hmid⟩ := sim_wrapped_of_reaches M2to1 a b_mid (hx ▸ b_reach)
      rw [hmid, relabel_step] at hstep
      simp only [Option.map_eq_some_iff] at hstep
      obtain ⟨a'', ha'', heq⟩ := hstep
      rw [← heq] at hy
      simp only [Turing.TM1.Cfg.mk.injEq] at hy
      obtain ⟨hl, hv, hT⟩ := hy
      have hb : a'' = b := by
        cases a''; cases b
        simp only [Turing.TM1.Cfg.mk.injEq]
        exact ⟨Option.map_injective (fun x y h => by cases h; rfl) hl, hv, hT⟩
      subst hb
      exact Relation.ReflTransGen.tail (ih a mid hx hmid) (by rw [Option.mem_def]; exact ha'')
  exact hgen _ _ h a b rfl rfl

theorem fixThenSim_eval_dom
    {K : Type u} {Γ : K → Type u} {Λ σ : Type u}
    [Inhabited Λ] [Inhabited σ] [DecidableEq K]
    (M : Λ → Turing.TM2.Stmt Γ Λ σ) (k : K) (L : List (Γ k)) :
    (Turing.TM1.eval (fixThenSim (Turing.TM2to1.tr M))
      (trInitAllFalse k L)).Dom ↔
    (Turing.TM2.eval M k L).Dom := by
  rw [← Turing.TM2to1.tr_eval_dom]
  simp only [Turing.TM1.eval, Part.dom_iff_mem]
  constructor
  · intro ⟨a, ha⟩
    rw [Part.mem_map_iff] at ha
    obtain ⟨c, hc, rfl⟩ := ha
    rw [Turing.mem_eval] at hc
    obtain ⟨hreaches, hhalt⟩ := hc
    have hfix := fix_step M k L
    have hreaches2 : Turing.Reaches (Turing.TM1.step (fixThenSim (Turing.TM2to1.tr M)))
            ⟨some (FixThenSimLabel.sim (default : Turing.TM2to1.Λ' K Γ Λ σ)), default,
              (Turing.TM1.init (Turing.TM2to1.trInit k L) :
                Turing.TM1.Cfg (Turing.TM2to1.Γ' K Γ) (Turing.TM2to1.Λ' K Γ Λ σ) σ).Tape⟩ c := by
      rcases Relation.ReflTransGen.cases_head hreaches with rfl | ⟨c', hstep, hrest⟩
      · simp [hfix] at hhalt
      · rw [Option.mem_def] at hstep
        rw [hfix] at hstep
        injection hstep with hstep
        rw [hstep]
        exact hrest
    obtain ⟨c', rfl⟩ := sim_wrapped_of_reaches (Turing.TM2to1.tr M)
      ⟨some default, default, (Turing.TM1.init (Turing.TM2to1.trInit k L) :
        Turing.TM1.Cfg (Turing.TM2to1.Γ' K Γ) (Turing.TM2to1.Λ' K Γ Λ σ) σ).Tape⟩
      c hreaches2
    refine ⟨c'.Tape.right₀, ?_⟩
    rw [Part.mem_map_iff]
    refine ⟨c', ?_, rfl⟩
    rw [Turing.mem_eval]
    constructor
    · -- Reaches
      exact relabel_reaches_inv (Turing.TM2to1.tr M)
        ⟨some default, default, (Turing.TM1.init (Turing.TM2to1.trInit k L) :
          Turing.TM1.Cfg (Turing.TM2to1.Γ' K Γ) (Turing.TM2to1.Λ' K Γ Λ σ) σ).Tape⟩
        c' hreaches2
    · -- Halt
      have h := relabel_step (Turing.TM2to1.tr M) c'
      rw [hhalt] at h
      cases hstep : Turing.TM1.step (Turing.TM2to1.tr M) c' with
      | none => rfl
      | some c'' => simp [hstep] at h
  · intro ⟨a, ha⟩
    rw [Part.mem_map_iff] at ha
    obtain ⟨c, hc, rfl⟩ := ha
    rw [Turing.mem_eval] at hc
    obtain ⟨hreaches, hhalt⟩ := hc
    refine ⟨c.Tape.right₀, ?_⟩
    rw [Part.mem_map_iff]
    refine ⟨⟨c.l.map FixThenSimLabel.sim, c.var, c.Tape⟩, ?_, rfl⟩
    rw [Turing.mem_eval]
    constructor
    · -- Reaches: fix step then relabel_reaches
      apply Relation.ReflTransGen.head
      · rw [Option.mem_def]
        exact fix_step M k L
      · exact relabel_reaches (Turing.TM2to1.tr M)
          ⟨some default, default, (Turing.TM1.init (Turing.TM2to1.trInit k L) :
            Turing.TM1.Cfg (Turing.TM2to1.Γ' K Γ) (Turing.TM2to1.Λ' K Γ Λ σ) σ).Tape⟩
          c hreaches
    · -- Halt
      have h := relabel_step (Turing.TM2to1.tr M) c
      rw [hhalt] at h
      simpa using h

lemma every_tm2_recognisable_language_is_tm1_recognisable {Γ : Type u}
    [Inhabited Γ] [FinEnum Γ]
    (L : Language Γ)
    (hL : L ∈ languagesRecognisedByTM2s) :
    L ∈ languagesRecognisedByTM1s := by
  obtain ⟨K, _, hKfin, hKdec, Γ', hΓ'inh, hΓ'fin, hΓ'dec, h, Λ, hΛinh, σ, hσinh,
    hσfin, M, S, hS, hLeq⟩ := hL
  haveI : ∀ k, DecidableEq (Γ' k) := hΓ'dec
  haveI : DecidableEq (Turing.TM2to1.Γ' K Γ') := instDecidableEqProd
  -- The TM1 encoding: inject Γ into Turing.TM2to1.Γ' K Γ' via the default stack
  let enc : Γ → Turing.TM2to1.Γ' K Γ' :=
    fun a => (false, Function.update (fun _ ↦ none) default (some (h ▸ a)))
  refine ⟨Turing.TM2to1.Γ' K Γ',
    Turing.TM2to1.Γ'.inhabited,
    Turing.TM2to1.Γ'.fintype,
    inferInstance,
    enc,
    ?_, ?_,
    FixThenSimLabel (Turing.TM2to1.Λ' K Γ' Λ σ),
    inferInstance,
    σ, hσinh, hσfin,
    fixThenSim (Turing.TM2to1.tr M),
    (fixThenSim_supports M (Turing.TM2to1.trSupp M S)
      (Turing.TM2to1.tr_supports M hS)).choose,
    (fixThenSim_supports M (Turing.TM2to1.trSupp M S)
      (Turing.TM2to1.tr_supports M hS)).choose_spec,
    ?_⟩
  · -- enc is injective
    intro a b hab
    simp only [enc] at hab
    have h2 : Function.update (fun _ ↦ none) default (some (h ▸ a)) =
              Function.update (fun _ ↦ none) default (some (h ▸ b)) :=
      (Prod.mk.inj hab).2
    have h3 : (h ▸ a : Γ' default) = (h ▸ b : Γ' default) := by
      have := congr_fun h2 default
      simp only [Function.update_self, Option.some.injEq] at this
      exact this
    cases h; exact h3
  · -- default ∉ range enc
    intro ⟨a, ha⟩
    simp only [enc] at ha
    have h1 : (false, Function.update (fun _ ↦ none) default (some (h ▸ a))) =
              (default : Turing.TM2to1.Γ' K Γ') := ha
    have h2 := (Prod.mk.inj h1).1
    simp at h2
    have h3 := (Prod.mk.inj ha).2
    simp at h3
  · -- L equals the recognised language
    subst hLeq
    ext input
    simp only [Set.mem_setOf_eq, enc]
    cases h
    rw [show List.map (fun a => (false, Function.update (fun _ ↦ none) default (some a))) input =
          trInitAllFalse default input.reverse from by
      simp [trInitAllFalse]]
    simp only
    exact (fixThenSim_eval_dom M default input.reverse).symm

end RandomisedGeneration
