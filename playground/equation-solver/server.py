#!/usr/bin/env python3
"""
Simple Flask server that uses Z3 to solve equations.
This demonstrates Z3 SMT solver with a clean web interface.

Run: python server.py
Then open: http://localhost:5000
"""

from flask import Flask, request, jsonify, send_file
from flask_cors import CORS
from z3 import *
import os

app = Flask(__name__)
CORS(app)  # Enable CORS for local development

@app.route('/')
def index():
    """Serve the HTML page"""
    return send_file('index-backend.html')

@app.route('/solve', methods=['POST'])
def solve_equations():
    """
    Solve system of linear equations:
    x + y = a
    x - y = b
    
    Returns: {x: value, y: value, status: 'sat'|'unsat'}
    """
    try:
        data = request.get_json()
        a = int(data.get('a', 0))
        b = int(data.get('b', 0))
        
        print(f"Solving: x + y = {a}, x - y = {b}")
        
        # Create Z3 solver
        solver = Solver()
        
        # Create variables
        x = Int('x')
        y = Int('y')
        
        # Add constraints
        solver.add(x + y == a)
        solver.add(x - y == b)
        
        # Solve
        result = solver.check()
        
        if result == sat:
            model = solver.model()
            x_val = model[x].as_long()
            y_val = model[y].as_long()
            
            print(f"Solution: x = {x_val}, y = {y_val}")
            
            return jsonify({
                'status': 'sat',
                'x': x_val,
                'y': y_val,
                'message': f'Solution found: x = {x_val}, y = {y_val}'
            })
        else:
            return jsonify({
                'status': 'unsat',
                'message': 'No solution exists'
            })
            
    except Exception as e:
        print(f"Error: {e}")
        return jsonify({
            'status': 'error',
            'message': str(e)
        }), 500

if __name__ == '__main__':
    print("Starting Z3 Equation Solver Server...")
    print("Open http://localhost:5000 in your browser")
    app.run(debug=True, port=5000)

