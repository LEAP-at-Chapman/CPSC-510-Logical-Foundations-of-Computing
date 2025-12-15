Download Files:
- [Python Script](./llm_autoformalize.py)
- [requirements.txt](./requirements.txt)
- [Run Bash Script](./run.sh)

```python
import sys
import json
import re
from pathlib import Path
from textwrap import dedent

import ollama


MODEL = "qwen3:30b"
CLIENT = ollama.Client(host='http://dgx0.chapman.edu:11434')


def load_few_shot_examples(data_dir="/wu_autoformalizations", num_examples=30, per_file=10):
    examples = []
    data_path = Path(data_dir)
    
    for json_file in sorted(data_path.glob("*.json")):
        file_examples = 0
        with open(json_file, 'r') as f:
            for line in f:
                if file_examples >= per_file:
                    break
                try:
                    example = json.loads(line.strip())
                    problem_prompt = example.get('problem_prompt', '')
                    nl_match = re.search(r'Natural language version: "(.*?)"', problem_prompt, re.DOTALL)
                    natural_language = nl_match.group(1) if nl_match else ""
                    
                    if natural_language and example.get('response'):
                        examples.append({
                            'natural': natural_language.strip(),
                            'isabelle': example['response'].strip()
                        })
                        file_examples += 1
                except:
                    continue
        
        if len(examples) >= num_examples:
            break
    
    return examples


def build_prompt(problem, few_shot_examples):
    prompt = dedent("""
        You are an expert at formalizing mathematical problems into Isabelle/HOL theorem statements.

        Convert the natural language math problem into formal Isabelle/HOL syntax.

        Guidelines:
        - Use 'theorem' to start
        - Declare variables with 'fixes' and types (real, int, nat, complex)
        - State assumptions with 'assumes' (use h0, h1, h2 labels)
        - State the goal with 'shows'
        - Use Isabelle syntax: 'powr' for exponentiation, 'sqrt' for square roots, '*' for multiplication

        Examples:

    """).strip() + "\n\n"
    
    for i, ex in enumerate(few_shot_examples[:3], 1):
        prompt += f"Example {i}:\n"
        prompt += f'Natural: "{ex["natural"]}"\n\n'
        prompt += f"Isabelle:\n{ex['isabelle']}\n\n"
    
    prompt += f'Now formalize:\nNatural: "{problem}"\n\nIsabelle:\n'
    return prompt


def formalize_with_ollama(problem, few_shot_examples):
    prompt = build_prompt(problem, few_shot_examples)
    
    try:
        result = []
        
        stream = CLIENT.generate(
            model=MODEL,
            prompt=prompt,
            stream=True,
            options={
                "temperature": 0.2,
                "top_p": 0.9
            }
        )
        
        for chunk in stream:
            token = chunk.get('response', '')
            print(token, end='', flush=True)
            result.append(token)
        
        print()
        return ''.join(result).strip()
    except Exception as e:
        return f"\nError: {str(e)}"
def main():
    print("Loading few-shot examples...")
    few_shot_examples = load_few_shot_examples()
    
    if not few_shot_examples:
        print("Warning: No examples loaded")
    else:
        print(f"Loaded {len(few_shot_examples)} examples\n")
    
    print("=" * 80)
    print("AUTOFORMALIZATION")
    print(f"Model: {MODEL}")
    print("=" * 80)
    print("Type 'quit' to exit\n")
    
    while True:
        problem = input("Enter problem: ").strip()
        
        if not problem:
            continue
            
        if problem.lower() in ['quit', 'exit', 'q']:
            break
        
        print("\nNatural Language:")
        print(f"  {problem}")
        print("\nIsabelle/HOL:\n  ", end='', flush=True)
        result = formalize_with_ollama(problem, few_shot_examples)
        print("\n" + "=" * 80 + "\n")


if __name__ == "__main__":
    main()
```