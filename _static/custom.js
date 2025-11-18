// Adjust section numbering to start at 0
(function() {
    function decrementNumber(text) {
        // Match patterns like "1. Title", "1.1 Title", "1.1.1 Title", etc.
        const match = text.match(/^(\d+)((\.\d+)*)\s+(.+)$/);
        if (match) {
            const firstNum = parseInt(match[1]);
            if (firstNum > 0) {
                const newFirstNum = firstNum - 1;
                const rest = match[2]; // e.g., ".1" or ".1.2"
                const title = match[4];
                return newFirstNum + rest + ' ' + title;
            }
        }
        return text;
    }
    
    function adjustNumbering() {
        // Adjust all headings (h1, h2, h3, h4, etc.)
        document.querySelectorAll('h1, h2, h3, h4, h5, h6').forEach(function(heading) {
            const originalText = heading.textContent || heading.innerText;
            const newText = decrementNumber(originalText);
            if (newText !== originalText) {
                heading.textContent = newText;
            }
        });
        
        // Adjust numbers in table of contents and sidebar
        document.querySelectorAll('.toctree-wrapper a, .bd-toc a, .bd-sidebar a, nav a').forEach(function(link) {
            const originalText = link.textContent || link.innerText;
            const newText = decrementNumber(originalText);
            if (newText !== originalText) {
                link.textContent = newText;
            }
        });
        
        // Adjust numbers in page titles
        const titleElement = document.querySelector('title');
        if (titleElement) {
            const originalText = titleElement.textContent || titleElement.innerText;
            const newText = decrementNumber(originalText);
            if (newText !== originalText) {
                titleElement.textContent = newText;
            }
        }
    }
    
    // Run when DOM is ready
    if (document.readyState === 'loading') {
        document.addEventListener('DOMContentLoaded', adjustNumbering);
    } else {
        adjustNumbering();
    }
    
    // Also run after delays to catch dynamically loaded content
    setTimeout(adjustNumbering, 100);
    setTimeout(adjustNumbering, 500);
})();

