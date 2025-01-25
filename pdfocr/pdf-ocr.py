import pdf2image
import numpy as np
from PIL import Image
import pytesseract
from typing import Tuple, List, Dict
import logging

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

class CharacterLocator:
    def __init__(self, min_region_size: int = 10):
        """
        Initialize the character locator.
        
        Args:
            min_region_size: Minimum size of region to consider for character detection
        """
        self.min_region_size = min_region_size
        
    def is_region_empty(self, image: np.ndarray, threshold: float = 0.99) -> bool:
        """
        Check if a region is effectively empty (mostly white).
        
        Args:
            image: numpy array of the image region
            threshold: whiteness threshold (0-1)
            
        Returns:
            bool: True if region is empty
        """
        if len(image.shape) == 3:
            # Convert to grayscale if color
            image = np.mean(image, axis=2)
        
        # Normalize to 0-1
        image = image / 255.0
        
        # Calculate average whiteness
        whiteness = np.mean(image)
        return whiteness > threshold
    
    def get_character_at_region(self, image: np.ndarray) -> str:
        """
        Attempt to recognize a single character in the given region.
        
        Args:
            image: numpy array of the image region
            
        Returns:
            str: recognized character or empty string if none found
        """
        # Convert numpy array to PIL Image
        pil_image = Image.fromarray(image)
        
        # Use tesseract with specific config for single character
        config = '--psm 10'  # Treat image as single character
        try:
            char = pytesseract.image_to_string(pil_image, config=config).strip()
            return char if len(char) == 1 else ''
        except Exception as e:
            logger.warning(f"Error in OCR: {e}")
            return ''
    
    def analyze_region(self, 
                      image: np.ndarray, 
                      x: int, 
                      y: int, 
                      width: int, 
                      height: int) -> List[Dict]:
        """
        Recursively analyze a region of the image to find characters.
        
        Args:
            image: Full page image as numpy array
            x, y: Top-left corner coordinates of region
            width, height: Dimensions of region
            
        Returns:
            List of dicts containing character and location information
        """
        results = []
        
        # Extract the region
        region = image[y:y+height, x:x+width]
        
        # Base cases
        if width < self.min_region_size or height < self.min_region_size:
            return results
        
        if self.is_region_empty(region):
            return results
        
        # Try to recognize a single character
        char = self.get_character_at_region(region)
        if char:
            results.append({
                'char': char,
                'x': x,
                'y': y,
                'width': width,
                'height': height
            })
            return results
        
        # If no single character found, split region and recurse
        half_width = width // 2
        half_height = height // 2
        
        # Analyze quadrants
        quadrants = [
            (x, y, half_width, half_height),
            (x + half_width, y, width - half_width, half_height),
            (x, y + half_height, half_width, height - half_height),
            (x + half_width, y + half_height, width - half_width, height - half_height)
        ]
        
        for qx, qy, qw, qh in quadrants:
            results.extend(self.analyze_region(image, qx, qy, qw, qh))
            
        return results

def process_pdf(pdf_path: str) -> Dict[int, List[Dict]]:
    """
    Process a PDF file and locate characters on each page.
    
    Args:
        pdf_path: Path to the PDF file
        
    Returns:
        Dict mapping page numbers to lists of character locations
    """
    # Convert PDF to images
    pages = pdf2image.convert_from_path(pdf_path)
    
    locator = CharacterLocator()
    results = {}
    
    for page_num, page in enumerate(pages, 1):
        print(f"Processing page {page_num}")
        logger.info(f"Processing page {page_num}")
        
        # Convert to numpy array
        page_array = np.array(page)
        
        # Get page dimensions
        height, width = page_array.shape[:2]
        
        # Analyze full page
        page_results = locator.analyze_region(page_array, 0, 0, width, height)
        
        results[page_num] = page_results
        
        print(f"Found {len(page_results)} characters on page {page_num}")
        logger.info(f"Found {len(page_results)} characters on page {page_num}")
        
    return results

def main():
    import argparse
    import json
    
    parser = argparse.ArgumentParser(description='Extract character locations from PDF')
    parser.add_argument('pdf_path', help='Path to PDF file')
    parser.add_argument('output_path', help='Path for JSON output file')
    
    args = parser.parse_args()
    
    try:
        results = process_pdf(args.pdf_path)
        
        # Save results to JSON
        with open(args.output_path, 'w') as f:
            json.dump(results, f, indent=2)
            
        logger.info(f"Results saved to {args.output_path}")
        
    except Exception as e:
        logger.error(f"Error processing PDF: {e}")
        raise

if __name__ == "__main__":
    main()
